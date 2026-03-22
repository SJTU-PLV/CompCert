Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Rustlight RustIR RustIRcfg.
Require Import InitDomain InitAnalysis.

Import ListNotations.

Local Open Scope error_monad_scope.

(** Use the analysis from InitAnalysis.v to elaborate the drop
statements. After this pass, the ownership semantics is removed. The
memory deallocation would be explicit and deterministic *)

(** The drop elaboration has three steps: 1. Analyze the initialized place at each point of the CFG; 2. Iterate the CFG to
collect drop flags for each drops; 3. Update the drops statement (from
conditonally drop to deterministic drop) in RustIR (AST) and insert
the update of the drop flag before the occurence of ownership transfer
*)


Parameter fresh_atom: place -> ident.

(** Step 1: generate drop flags for the places whose init information
is flow-sensitive.  *)

Fixpoint generate_drop_flags_for_splits (mayinit mayuninit universe: PathsMap.t) (l: list place) : list (place * ident) :=
  match l with
  | nil => nil
  | p :: l' =>
      let flags := generate_drop_flags_for_splits mayinit mayuninit universe l' in
      if negb (drop_type (typeof_place p)) then
        (* we do not need to generate drop flag for scalar typed place *)
        flags
      else
        if must_init mayinit mayuninit universe p then
          (* this place must be init, no need for drop flag *)
          flags
        else if may_init mayinit mayuninit universe p then
               (* need drop flag *)
               let drop_flag := fresh_atom p in
               (p, drop_flag) :: flags
             else
               (* this place must be uninit, no need to drop *)
               flags
  end.

Definition generate_drop_flags_for (mayinit mayuninit universemap: PathsMap.t) (ce: composite_env) (p: place) : list (place * ident) :=
  let universe := PathsMap.get (local_of_place p) universemap in
  match split_drop_place ce universe p (typeof_place p) with
  | OK drop_places =>      
      (** may be we should check the disjointness of drop flags *)
      generate_drop_flags_for_splits mayinit mayuninit universemap (map fst drop_places)
  (* The error case is considerer in elaboration step *)
  | Error msg =>
      []
  end.

Definition generate_place_map_fun {A: Type} := (fun m (elt: place * A) => let id := local_of_place (fst elt) in
                       match PTree.get id m with
                       | Some l =>
                           PTree.set id (elt :: l) m
                       | None =>
                           PTree.set id [elt] m
                       end).

Definition generate_place_map {A} (l: list (place * A)) : PTree.t (list (place * A)) :=
  fold_left generate_place_map_fun l
    (PTree.empty (list (place * A))).

Section INIT_UNINIT.


Variable (maybeInit maybeUninit: PMap.t IM.t).
Variable universe : PathsMap.t.

Definition generate_drop_flags_at (ce: composite_env) (f: function) (pc: node) (instr: instruction) : list (place * ident) :=
  match maybeInit!!pc, maybeUninit!!pc with
  | IM.State mayinit, IM.State mayuninit =>
      match instr with
      | Isel sel _ =>
          match select_stmt f.(fn_body) sel with
          | Some (Sdrop p) =>
              generate_drop_flags_for mayinit mayuninit universe ce p
          | _ => []
          end
      | _ => []     
      end
  | _, _ => []
  end.


Definition generate_drop_flags (ce: composite_env) (f: function) (cfg: rustcfg) : Errors.res (list (place * ident)) :=
  let flags := concat (map snd (PTree.elements (PTree.map (generate_drop_flags_at ce f) cfg))) in
  if list_norepet_dec place_eq (map fst flags) then
    if list_norepet_dec ident_eq (map snd flags) then
      OK flags
    else
      Error (msg "Repeated drop flags in generate_drop_flags")
  else
    Error (msg "Repeated drop places in generate_drop_flags")
.

End INIT_UNINIT.


(** Step 2: elaborate the statement in the AST by iterating the CFG *)

Definition get_dropflag_temp (m: PTree.t (list (place * ident))) (p: place) : option ident :=
  let id := local_of_place p in
  match m!id with
  | Some l =>
      match find (fun elt => place_eq p (fst elt)) l with
      | Some (_, fid) => Some fid
      | _ => None
      end
  | _ => None
  end.

(* Some functions of setting drop flags  *)

Definition Ibool (b: bool) := Epure (Econst_int (if b then Int.one else Int.zero) type_bool).

Definition set_dropflag (id: ident) (flag: bool) : statement :=
  Sassign (Plocal id type_bool) (Ibool flag).

Definition set_dropflag_option (id: option ident) (flag: bool) : statement :=
  match id with
  | Some id =>
      set_dropflag id flag
  | None => Sskip
  end.


(* generate drop statements *)

Definition drop_fully_own (p: place) :=
  makeseq (map (fun p => Sdrop p) (Rustlightown.split_fully_own_place p (typeof_place p))).

(* create a drop statement using drop flag optionally *)
Definition generate_drop (p: place) (full: bool) (flag: option ident) : statement :=
  let drop := if full then
                drop_fully_own p
                (* To simulate makeseq *)
              else Ssequence (Sdrop p) (Ssequence Sskip Sskip) in
  match flag with
  | Some id =>
      let set_flag := set_dropflag id false in
      Sifthenelse (Epure (Eplace (Plocal id type_bool) type_bool)) (Ssequence set_flag drop) Sskip
  | None => drop
  end.


Fixpoint elaborate_drop_for_splits (mayinit mayuninit universe: PathsMap.t) (flagm: PTree.t (list (place * ident))) (l: list (place * bool)) : statement :=
  match l with
  | nil => Sskip
  | (p, full) :: l' =>
      let stmt := elaborate_drop_for_splits mayinit mayuninit universe flagm l' in
      if negb (drop_type (typeof_place p)) then
        (* no need to generate drop for scalar typed places *)
        (Ssequence Sskip stmt)
      else
        (* use flagm to decide whether insert drop flag or not *)
        match get_dropflag_temp flagm p with
        | Some id =>
            (* need drop flag *)
            (Ssequence (generate_drop p full (Some id)) stmt)
        | None =>
            if must_init mayinit mayuninit universe p then
              (Ssequence (generate_drop p full None) stmt)
            else
              (* this place must be uninit, no need to drop *)
              (Ssequence Sskip stmt)
        end
  end.

Definition elaborate_drop_for (mayinit mayuninit universemap: PathsMap.t) (ce: composite_env) (flagm: PTree.t (list (place * ident))) (p: place) : Errors.res statement :=
  let universe := PathsMap.get (local_of_place p) universemap in
  do drop_places <- split_drop_place ce universe p (typeof_place p);
      (** may be we should check the disjointness of drop flags. Use a skip to simulate source step_to_dropplace *)
  OK (Ssequence Sskip (elaborate_drop_for_splits mayinit mayuninit universemap flagm drop_places))
.


Section ELABORATE.

(* map from place to its drop flag *)
Variable m: PTree.t (list (place * ident)).
Variable ce: composite_env.

Fixpoint set_dropflag_for_splits (l: list place) (flag: bool) : statement :=
  match l with
  | nil => Sskip
  | p :: l' =>
      Ssequence (set_dropflag_option (get_dropflag_temp m p) flag) (set_dropflag_for_splits l' flag)
  end.

Definition add_dropflag (universeMap: PathsMap.t) (p: place) (flag: bool) : Errors.res statement :=
  let universe := PathsMap.get (local_of_place p) universeMap in
  do drop_places <- split_drop_place ce universe p (typeof_place p);
  OK (set_dropflag_for_splits (map fst drop_places) flag).

Definition add_dropflag_option universeMap (p: option place) (flag: bool) : Errors.res statement :=
  match p with
  | Some p => add_dropflag universeMap p flag
  | _ => OK Sskip
  end.

Fixpoint add_dropflag_list universeMap (l: list place) (flag: bool) : Errors.res statement :=
  match l with
  | nil => OK Sskip
  | p :: l' =>
      do s1 <- add_dropflag universeMap p flag;
      do s2 <- add_dropflag_list universeMap l' flag;
      OK (Ssequence s1 s2)
  end.
     

(* Instance of transl_stmt in the transl_on_cfg. [an] is (mayinit,
mayuninit, universe) *)
Definition elaborate_stmt (an: IM.t * IM.t * PathsMap.t) (stmt: statement) : Errors.res statement :=
  let '(mayInit, mayUninit, universe) := an in
  match mayInit, mayUninit with
  | IM.State mayinit, IM.State mayuninit =>      
      match stmt with
      | Sdrop p =>
          elaborate_drop_for mayinit mayuninit universe ce m p
      | Sassign p e
      | Sassign_variant p _ _ e
      | Sbox p e =>
          let deinit := moved_place e in
          do stmt1 <- add_dropflag_option universe deinit false;
          do stmt2 <- add_dropflag universe p true;
          OK (Ssequence stmt1 (Ssequence stmt2 stmt))
      | Scall p e el =>
          let mvpaths := moved_place_list el in
          do stmt1 <- add_dropflag_list universe mvpaths false;
          do stmt2 <- add_dropflag universe p true;
          OK (Ssequence (Ssequence stmt1 stmt) stmt2)
      | _ => OK stmt
      end
  (* impossible *)
  | _, _ => OK stmt
  end.
      

End ELABORATE.


Local Open Scope error_monad_scope.

Definition init_drop_flag (mayinit mayuninit universe: PathsMap.t) (p: place) (flag: ident) : Errors.res statement :=
  if must_init mayinit mayuninit universe p then
    OK (set_dropflag flag true)
  else
    (* impossible: return error *)
    if may_init mayinit mayuninit universe p then
      Error (msg "impossible may_init in init_drop_flag")           
    else      
      (* how to show that must_init = false is must_unowed in function
         entry *)
      OK (set_dropflag flag false).
  (* let id := local_of_place p in *)
  (* match mayinit!id, mayuninit!id with *)
  (* | Some init, Some uninit => *)
  (*     if Paths.mem p init then *)
  (*       set_dropflag flag true *)
  (*     else *)
  (*       if Paths.mem p uninit then *)
  (*         set_dropflag flag false *)
  (*       else Sskip *)
  (* | _, _ => Sskip *)
  (* end. *)

Fixpoint init_drop_flags (mayinit mayuninit universe: PathsMap.t) (flags: list (place * ident)) : Errors.res statement :=
  match flags with
  | nil => OK Sskip
  | (p, flag) :: flags' =>
      do stmt <- init_drop_flags mayinit mayuninit universe flags';
      do init <- init_drop_flag mayinit mayuninit universe p flag;
      OK (Ssequence init stmt)
  end.

Definition init_drop_flags_bot (mayInit mayUninit: IM.t) (universe: PathsMap.t) (flags: list (place * ident)) : Errors.res statement :=
  match mayInit, mayUninit with
  | IM.State mayinit, IM.State mayuninit =>      
      init_drop_flags mayinit mayuninit universe flags
  | _, _ =>
      Error (msg "impossible in init_drop_flags_bot")
  end.

Definition uncheck_expr : (IM.t * IM.t * PathsMap.t) -> expr -> Errors.res unit := (fun _ _ => OK tt).
  
Definition transf_function (ce: composite_env) (f: function) : Errors.res function :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  do analysis_res <- analyze ce f cfg entry;
  let '(mayinit, mayuninit, universe) := analysis_res in
  let vars := var_names (f.(fn_vars) ++ f.(fn_params)) in
  (** step 1: generate drop flags *)
  do flags <- generate_drop_flags mayinit mayuninit universe ce f cfg;
  (* check the disjointness between the drop flags and the variales *)
  if list_disjoint_dec ident_eq (map snd flags) (map fst (f.(fn_params) ++ f.(fn_vars))) then
    let flagm := generate_place_map flags in
    (** step 2: elaborate the statements *)
    do stmt <- transl_on_cfg get_init_info (mayinit, mayuninit, universe) (elaborate_stmt flagm ce) uncheck_expr f.(fn_body) cfg;
    (** step 3: initialize drop flags *)
    let entry_init := mayinit!!entry in
    let entry_uninit := mayuninit!!entry in
    (* init drop flags: if no flags, it would be a Sskip *)
    do init_stmt <- init_drop_flags_bot entry_init entry_uninit universe flags;
    let flag_vars := combine (map snd flags) (repeat type_bool (length flags)) in
    Errors.OK (mkfunction f.(fn_generic_origins)
                          f.(fn_origins_relation)
                          f.(fn_drop_glue)
                          f.(fn_param_types)
                          f.(fn_return)
                          f.(fn_callconv)
                          (f.(fn_vars) ++ flag_vars)
                          f.(fn_params)
                          (Ssequence init_stmt stmt))
  else
    Error (msg "The generated drop flags are overlap with the parameters and variables") 
  . 


Definition transf_fundef (ce: composite_env) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f => do tf <- transf_function ce f; Errors.OK (Internal tf)
  | External orgs org_rels ef targs tres cconv => Errors.OK (External orgs org_rels ef targs tres cconv)
  end.


(** Translation of a whole program. *)

Definition transl_program (p: program) : Errors.res program :=
  do p1 <- transform_partial_program (transf_fundef p.(prog_comp_env)) p;
  Errors.OK {| prog_defs := AST.prog_defs p1;
              prog_public := AST.prog_public p1;
              prog_main := AST.prog_main p1;
              prog_types := prog_types p;
              prog_comp_env := prog_comp_env p;
              prog_comp_env_eq := prog_comp_env_eq p |}.
