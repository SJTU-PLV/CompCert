Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import RustlightBase RustIR.
Require Import Initialized.

Local Open Scope error_monad_scope.

(** Use the analysis from Initialized.v to elaborate the drop
statements. After this pass, the ownership semantics is removed. The
memory deallocation would be explicit and deterministic *)

(** The drop elaboration has three steps: 1. Iterate the CFG to
collect drop flags for each drops; 2. During the iteration, update the
drops statement (from conditonally drop to deterministic drop) in
RustIR (AST); 3. Insert the update of the drop flag before the
occurence of ownership transfer *)

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type);
  gen_map: PMap.t (list (place * ident));
  gen_stmt: statement (* It is used for elaborating the drops when collecting drop flags *)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope gensym_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : gensym_monad_scope.

(* Parameter first_unusead_ident: unit -> ident. *)

(* for now we just use the maximum ident of parameters and variables
as the initial ident *)
Definition initial_generator (x: ident) (stmt: statement) : generator :=
  mkgenerator x nil (nil, PTree.empty (list (place * ident))) stmt.

(* generate a new drop flag with type ty (always bool) and map [p] to this flag *)
Definition gensym (ty: type) (p: place) : mon ident :=
  let id := local_of_place p in
  fun (g: generator) =>
    Res (gen_next g)
      (mkgenerator (Pos.succ (gen_next g))
         ((gen_next g, ty) :: gen_trail g)
         (PMap.set id ((p, (gen_next g)) :: (gen_map g) !! id) (gen_map g))
         (gen_stmt g))
      (Ple_succ (gen_next g)).

Definition set_stmt (sel: selector) (stmt: statement) : mon unit :=
  fun (g: generator) =>
    Res tt
      (mkgenerator (gen_next g)
         (gen_trail g)
         (gen_map g)
         (update_stmt (gen_stmt g) sel stmt))
      (Ple_refl (gen_next g)).


Local Open Scope gensym_monad_scope.

(* For each drop(p) statement, return list of places and their
optional drop flag. Each place is used to generate a deterministic
drop statement. For now, we do not consider fully owned or partial
moved Box types. *)
Fixpoint elaborate_drop_for (mayinit mayuninit universe: Paths.t) (fuel: nat) (ce: composite_env) (p: place) : mon (list (place * option ident)) :=
  match fuel with
  | O => error (msg "Running out of fuel in elaborate_drop_for")
  | S fuel' =>
      let elaborate_drop_for := elaborate_drop_for mayinit mayuninit universe fuel' ce in
      if Paths.mem p universe then
        match typeof_place p with        
        | Tstruct _ _
        | Tvariant _ _ => (* use drop function of this Tstruct (Tvariant) to drop p *)
            if Paths.mem p mayinit then
              if Paths.mem p mayuninit then (* need drop flag *)
                do drop_flag <- gensym type_bool p;
                ret ((p, Some drop_flag) :: nil)
              else                         (* must initialized *)
                ret ((p, None) :: nil)
            else                (* must uninitialized *)
              ret nil
        | Tbox ty _ =>
            (** TODO: we need to check if p is fully owned, in order
            to just use one function to drop all its successor *)
            (* first drop *p if necessary *)
            do drops <- elaborate_drop_for (Pderef p ty);
            if Paths.mem p mayinit then
              if Paths.mem p mayuninit then (* need drop flag *)
                do drop_flag <- gensym type_bool p;
                ret ((p, Some drop_flag) :: drops)
              else                         (* must initialized *)
                ret ((p, None) :: drops)
            else                (* must uninitialized *)
              ret drops
        | _ => error (msg "Normal types do not need drop: elaborate_drop_for")
        end
      else (* split p into its children and drop them *)
        match typeof_place p with
        | Tstruct id attr =>
            match ce!id with
            | Some co =>
                let children := map (fun elt => match elt with
                                             | Member_plain fid fty =>
                                                 Pfield p fid fty end)
                                  co.(co_members) in
                let rec elt acc :=
                  do drops <- acc;
                  do drops' <- elaborate_drop_for elt;
                  ret (drops' ++ drops) in
                fold_right rec (ret nil) children
            | None => error (msg "Unfound struct id in composite_env: elaborate_drop_for")
            end
        | Tbox _ _ => error (msg "Box does not exist in the universe set: elaborate_drop_for")
        | Tvariant _ _ => error (msg "Variant cannot be split: elaborate_drop_for")
        | _ => ret nil
        end
  end.
  

Section INIT_UNINIT.

Variable (maybeInit maybeUninit: PMap.t PathsMap.t).

(* create a drop statement using drop flag optionally *)
Definition generate_drop (p: place) (flag: option ident) : statement :=
  let drop := Sdrop p in
  match flag with
  | Some id =>     
      Sifthenelse (Epure (Eplace (Plocal id type_bool) type_bool)) drop Sskip
  | None => drop
  end.                        

(* Collect the to-drop places and its drop flag from a statement, meanwhile updating the statement *)
Definition elaborate_drop_at (ce: composite_env) (f: function) (instr: instruction) (pc: node) : mon unit :=
  match instr with
  | Isel sel _ =>
      match select_stmt f.(fn_body) sel with
      | Some (Sdrop p) =>
          let mayinit := maybeInit!!pc in
          let mayuninit := maybeUninit!!pc in
          if  PathsMap.beq mayinit PathsMap.bot && PathsMap.beq mayuninit PathsMap.bot then
            error (msg "No initialized information: collect_elaborate_drops")
          else
            let id := local_of_place p in
            let init := PathsMap.get id mayinit in
            let uninit := PathsMap.get id mayuninit in
            let universe := Paths.union init uninit in
            (* drops are the list of to-drop places and their drop flags *)
            do drops <- elaborate_drop_for init uninit universe own_fuel ce p;
            let drop_stmts := map (fun elt => generate_drop (fst elt) (snd elt)) drops in
            set_stmt sel (makeseq drop_stmts)
      | _ => ret tt
      end
  | _ => ret tt
  end.

Definition elaborate_drop (ce: composite_env) (f: function) (cfg: rustcfg) : mon unit :=
  PTree.fold (fun _ pc elt => elaborate_drop_at ce f elt pc) cfg (ret tt).

End INIT_UNINIT.

(** Insert update of drop flags  *)

Section DROP_FLAGS.

(* map from place to its drop flag *)
Variable m: PTree.t (list (place * ident)).

Definition get_dropflag_temp (p: place) : option ident :=
  let id := local_of_place p in
  match m!id with
  | Some l =>
      match find (fun elt => place_eq p (fst elt)) l with
      | Some (_, fid) => Some fid
      | _ => None
      end
  | _ => None
  end.

Definition Ibool (b: bool) := Epure (Econst_int (if b then Int.one else Int.zero) type_bool).

Definition set_dropflag (id: ident) (flag: bool) : statement :=
  Sassign (Plocal id type_bool) (Ibool flag).

Definition set_dropflag_option (id: option ident) (flag: bool) : statement :=
  match id with
  | Some id =>
      set_dropflag id flag
  | None => Sskip
  end.

Definition add_dropflag (p: place) (flag: bool) : statement :=
  set_dropflag_option (get_dropflag_temp p) flag.


Definition add_dropflag_option (p: option place) (flag: bool) : statement :=
  match p with
  | Some p => add_dropflag p flag
  | _ => Sskip
  end.

Definition add_dropflag_list (l: list place) (flag: bool) : statement :=
  let stmts := fold_right (fun elt acc => add_dropflag elt flag :: acc) nil l in
  makeseq stmts.

(** FIXME: It may generate lots of Sskip *)
Fixpoint transl_stmt (stmt: statement) : statement :=
  match stmt with
  | Sassign p e
  | Sbox p e =>
      let deinit := moved_place e in
      let stmt1 := add_dropflag_option deinit false in
      let stmt2 := add_dropflag p true in
      makeseq (stmt1 :: stmt2 :: stmt :: nil)  
  | Scall p e el =>
      let mvpaths := moved_place_list el in
      let stmt1 := add_dropflag_list mvpaths false in
      let stmt2 := add_dropflag_option p true in
      makeseq (stmt1 :: stmt :: stmt2 :: nil)
  | Ssequence s1 s2 =>
      Ssequence (transl_stmt s1) (transl_stmt s2)
  | Sifthenelse e s1 s2 =>
      Sifthenelse e (transl_stmt s1) (transl_stmt s2)
  | Sloop s =>
      Sloop (transl_stmt s)
  | _ => stmt
  end.

End DROP_FLAGS.
  
Local Open Scope error_monad_scope.

Definition transf_function (ce: composite_env) (f: function) : Errors.res function :=
  do (mayinit, mayuninit) <- analyze ce f;
  let vars := var_names (f.(fn_vars) ++ f.(fn_params)) in
  let next_flag := Pos.succ (fold_left Pos.max vars 1%positive) in
  let init_state := initial_generator next_flag f.(fn_body) in
  (** FIXME: we generate cfg twice *)
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (* step 1 and step 2 *)
  match elaborate_drop mayinit mayuninit ce f cfg init_state with
  | Res _ st _ =>
      (* step 3: update drop flag *)          
      let stmt' := transl_stmt (snd st.(gen_map)) st.(gen_stmt) in
      Errors.OK (mkfunction f.(fn_return)
                        f.(fn_callconv)                        
                        (f.(fn_vars) ++ st.(gen_trail))
                        f.(fn_params)
                        stmt')      
  | Err msg =>
      Errors.Error msg
  end.


Definition transf_fundef (ce: composite_env) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f => do tf <- transf_function ce f; Errors.OK (Internal tf)
  | External _ ef targs tres cconv => Errors.OK (External function ef targs tres cconv)
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

