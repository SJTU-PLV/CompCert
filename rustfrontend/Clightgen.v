Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Clight.
Require Import Rustlight Rustlightown RustIR.
Require Import Errors.

Import ListNotations.

(** The generation from RustIR to Clight contains three steps:
1. translate the rust composite type (e.g., variant) to C composite
(variant is represented by a structure where the first field is tag
and the second is an union); 2. generate drop glue (function) for each
composite type which is movabl; 3. translate the RustIR statement to
Clight statement, while translating the drop to call free and box
construction to call malloc. *)


Local Open Scope error_monad_scope.

(** ** Step 1: Translate composite definitions *)

(* A uniform paramter id *)
Parameter param_id : ident.

(* get a fresh atom and update the next atom *)
Parameter fresh_atom: unit -> ident.

Parameter create_union_idents: ident -> (ident * ident * ident).

Definition transl_composite_member (m: member) : Ctypes.member :=
  match m with
  | Member_plain fid ty =>
      Ctypes.Member_plain fid (to_ctype ty)
  end.



(* Variant {a, b, c} => Struct {tag_fid: int; union_fid: {a,b,c}} . In
other word, the variant name is used as the tagged union struct name,
the constructor name (a,b,c) are used in the generated union *)
Definition transl_composite_def (* (union_map: PTree.t (ident * attr)) *) (co: composite_definition) : option (Ctypes.composite_definition * option Ctypes.composite_definition) :=
  match co with
  | Composite id Struct ms _ _ =>
      Some (Ctypes.Composite id Ctypes.Struct (map transl_composite_member ms) noattr, None)
  | Composite id TaggedUnion ms _ _ =>
      (* generate a Struct with two fields, one for the tag field and
      the other for the union *)
      let '(union_id, tag_fid, union_fid) := create_union_idents id in
      let tag_member := Ctypes.Member_plain tag_fid Ctypes.type_int32s in
      (* check the inequality between tag_fid and union_fid *)
      if ident_eq tag_fid union_fid then
        None
      else
        (* generate the union *)
        (** TODO: specify the attr  *)
        let union := (Ctypes.Composite union_id Union (map transl_composite_member ms) noattr) in
        let union_member := Ctypes.Member_plain union_fid (Tunion union_id noattr) in     
        Some (Ctypes.Composite id Ctypes.Struct (tag_member :: union_member :: nil) noattr, Some union)
  end.


(* Definition variant_to_union (co: composite_definition) : option (Ctypes.composite_definition * (ident * (ident * attr))) := *)
(*   match co with *)
(*   | Composite id Struct ms attr => None *)
(*   | Composite id TaggedUnion ms attr => *)
(*       let union_id := first_unused_ident tt in *)
(*       (** TODO: specify the attr  *) *)
(*       Some ((Ctypes.Composite union_id Union (map transl_composite_member ms) noattr), (id,(union_id, noattr))) *)
(*   end. *)

Definition flat_def (d: option (Ctypes.composite_definition * option Ctypes.composite_definition)) :=
  match d with
  (* utco must be afront of tco to make tco complete *)
  | Some (tco, Some utco) => [utco; tco]
  | Some (tco, None) => [tco]
  | None => []
  end.

(* Use link_composites to leverages existing lemmas *)
Definition transl_composites (l: list composite_definition) : option (list Ctypes.composite_definition) :=
  (* translate rust composite to C composite *)
  let defs := (map transl_composite_def l) in
  if forallb (fun elt => match elt with | Some _ => true | None => false end) defs then
    Some (flat_map flat_def defs)
    (* let (comps, unions_opt) := split defs in *)
    (* let unions :=  flat_map (fun elt => match elt with | Some u => [u] | None => [] end) unions_opt in *)
    (* Ctypes.link_composite_defs comps unions *)
  else
    None.

(** ** Step 2: Generate drop glue for each composite with ownership type *)


Fixpoint makeseq (l: list Clight.statement) : Clight.statement :=
  match l with
  (* To ensure that target program must move at least one step *)
  | nil => (Clight.Ssequence Clight.Sskip Clight.Sskip)
  | s :: l' => Clight.Ssequence s (makeseq l')
  end.


(* To specify *)
Parameter (malloc_id free_id: ident).

Require Ctyping.

Definition malloc_decl : (Ctypes.fundef Clight.function) :=
   (Ctypes.External EF_malloc (Ctypes.Tcons Ctyping.size_t Ctypes.Tnil) (Tpointer Ctypes.Tvoid noattr) cc_default).

Definition free_decl : (Ctypes.fundef Clight.function) :=
  (Ctypes.External EF_free (Ctypes.Tcons (Tpointer Ctypes.Tvoid noattr) Ctypes.Tnil) Tvoid cc_default).

Definition free_fun_expr : Clight.expr :=
  Evar free_id (Ctypes.Tfunction (Ctypes.Tcons (Tpointer Tvoid noattr) Ctypes.Tnil) Ctypes.Tvoid cc_default).

(* return [free(arg)], ty is the type arg points to, i.e. [arg: *ty] *)
Definition call_free (arg: Clight.expr) : Clight.statement :=
  Clight.Scall None free_fun_expr (arg :: nil).


Section COMPOSITE_ENV.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.

(* simulate deref_loc_rec *)
Fixpoint deref_arg_rec (headty: type) (arg: Clight.expr) (tys: list type) : Clight.expr :=
  match tys with
  | nil => arg
  | ty :: tys' =>
      (* load the value of ty *)
      (Ederef (deref_arg_rec ty arg tys') (to_ctype headty))
  end.

Lemma last_default_unrelate: forall A (l: list A) a d1 d2,
    last (a::l) d1 = last (a::l) d2
.
Proof.
  induction l;simpl; intros; auto.
  simpl in IHl.
  auto.
Qed.  
  
Lemma deref_arg_rec_app: forall tys1 tys2 hty arg,
    deref_arg_rec hty arg (tys1 ++ tys2) = deref_arg_rec hty (deref_arg_rec (last tys1 hty) arg tys2) tys1.
Proof.
  induction tys1.
  simpl. auto.
  simpl. intros. f_equal.
  destruct tys1.
  simpl. auto. erewrite IHtys1.
  erewrite last_default_unrelate. eauto.
Qed.


(* simulate drop_box_rec *)
Fixpoint drop_glue_for_box_rec (arg: Clight.expr) (tys: list type) : list Clight.statement :=
  match tys with
  | nil => nil
  | ty :: tys1 =>
      (* the value of ty. If we change tys1 to (ty::tys1) and use free(&arg), it is difficult to know the type ty points to. We just do not want to know the type of the block to be freed, we just need to know the type (here is ty) of the pointer points to this block *)
      let arg1 := deref_arg_rec ty arg tys1 in
      (* free(&arg1): because arg1 is the lvalue of the memory
      location to be freed, so we should pass the address of arg1 to
      free *)
      (* free(arg1): arg1 is the lvalue stores the memory location to be freed *)
      let free_stmt := call_free arg1 in
      (* let free_stmt := call_free (Eaddrof arg1 (Ctypes.Tpointer (Clight.typeof arg1) noattr)) in *)
      (* free the parent of arg1 *)
      free_stmt :: drop_glue_for_box_rec arg tys1
  end.

Definition call_composite_drop_glue (arg: Clight.expr) (ty: Ctypes.type) (drop_id: ident) :=
  let ref_arg_ty := (Ctypes.Tpointer ty noattr) in
  let glue_ty := Ctypes.Tfunction (Ctypes.Tcons ref_arg_ty Ctypes.Tnil) Tvoid cc_default in
  (* drop_in_place_xxx(&arg) *)
  let call_stmt := Clight.Scall None (Evar drop_id glue_ty) ((Eaddrof arg ref_arg_ty) :: nil) in
  call_stmt.

Definition drop_glue_for_type (m: PTree.t ident) (arg: Clight.expr) (ty: type) : Clight.statement :=
  (* we need to drop the value inside the tys = [ty1;ty2...;ty_n]. Evaluate
  arg would produce the value of ty_n *)
  let tys := drop_glue_children_types ty in
  match tys with
  | nil => Clight.Sskip
  | ty :: tys1 =>
      match ty with
      | Tvariant _ id
      | Tstruct _ id =>
          let arg1 := deref_arg_rec ty arg tys1 in
          (* We must guarantee that ty = typeof arg *)
          match m ! id with
          | None => Clight.Sskip
          | Some id' =>
              Clight.Ssequence (call_composite_drop_glue arg1 (Clight.typeof arg1) id') (makeseq (drop_glue_for_box_rec arg tys1))
          end
      | _ => makeseq (drop_glue_for_box_rec arg tys)
      end
  end.
  

(* Some example: 
drop_in_place_xxx(&Struct{a,b,c} param) {
    drop_in_place_a(&((deref param).a));
    drop_in_place_a(&((deref param).b));
    drop_in_place_a(&((deref param).c));
} *)

(* we assume deref_param is the dereference of the parameter *)
Definition drop_glue_for_member (m: PTree.t ident) (p: Clight.expr) (memb: member) : Clight.statement :=
  match memb with
  | Member_plain fid ty =>
      (* Use own_type here because type_to_drop_member_state uses own_type *)      
      if drop_type ty then
        let cty := (to_ctype ty) in
        let arg := Efield p fid cty in
        drop_glue_for_type m arg ty
      else
        Clight.Sskip
  end.

Fixpoint drop_glue_for_members (m: PTree.t ident) (p: Clight.expr) (membs: members) : Clight.statement :=
  match membs with
  | nil => Clight.Sskip
  | memb :: membs' =>
      (* may generate lots of Sskip but it is necessary to simulate
      the source semantics *)
      Clight.Ssequence (drop_glue_for_member m p memb) (drop_glue_for_members m p membs')
  end.

Fixpoint make_labelled_drop_stmts (m: PTree.t ident) (p: Clight.expr) (idx: Z) (membs: members) :=
  match membs with
  | [] => LSnil
  | memb :: membs' =>
      let ls := make_labelled_drop_stmts m p (idx+1) membs' in 
      LScons (Some idx) (Clight.Ssequence (drop_glue_for_member m p memb) Clight.Sbreak) ls
  end.
  
(* m: maps composite id to drop function id *)
Definition drop_glue_for_composite (m: PTree.t ident) (co_id: ident) (sv: struct_or_variant) (ms: members): option Clight.function :=
  (* The only function parameter *)
  let co_ty := (Ctypes.Tstruct co_id noattr) in
  let param_ty := Tpointer co_ty noattr in
  let deref_param := Ederef (Evar param_id param_ty) co_ty in
  match sv with
  | Struct =>
      let stmt_list := drop_glue_for_members m deref_param ms in
      (* an additonal skip statement to simulate the source semantics *)
      (Some (Clight.mkfunction Tvoid cc_default ((param_id, param_ty)::nil) nil nil (Clight.Ssequence Clight.Sskip stmt_list)))
  | TaggedUnion =>
      (* check tag and then call corresponded drop glue *)
      match tce ! co_id with
      | Some tco =>
          match tco.(co_su), tco.(Ctypes.co_members) with
          | Ctypes.Struct, Ctypes.Member_plain tag_id tag_ty :: Ctypes.Member_plain union_id union_ty :: nil =>
              (* get tag expr: *p.tag_id *)
              let get_tag := Efield deref_param tag_id tag_ty in
              let get_union := Efield deref_param union_id union_ty in
              (* use switch statements to model the pattern match? *)
              (* drops_list is [[case 0: drop(m1)];[case 1: drop(m2)]]*)
              (* let drops_list := fold_right (fun elt acc => (drop_glue_for_member m get_union elt) :: acc) (@nil (list Clight.statement)) ms in *)
              let drop_switch_branches := make_labelled_drop_stmts m get_union 0 ms in
              (* generate function *)
              let stmt := Clight.Sswitch get_tag drop_switch_branches in
              (Some (Clight.mkfunction Tvoid cc_default ((param_id, param_ty)::nil) nil nil stmt))
          (* This is impossible if tce is generated correctly *)
          | _, _ => None (* Error (msg "Variant is not correctly converted to C struct: drop_glue_for_composite") *)
          end
      (* This is impossible if tce is generated correctly *)
      | _ => None (* Error (msg "The conversion of variant does not exist in the C composite environment") *)
      end
  end.


Definition drop_glue_fundef (f: Clight.function) : (Ctypes.fundef Clight.function) :=
  (Ctypes.Internal f).

(** Generate drop glue for each composite that is movable *)

(* Definition generate_drops_list (l: list composite_definition) (dropm: PTree.t ident) : (list (ident * Clight.function)) := *)
(*   fold_right (fun '(Composite id sv membs a _ _) acc =>                            *)
(*                 let glue := drop_glue_for_composite dropm id sv membs a in *)
(*                 match glue with *)
(*                 | Some glue1 => *)
(*                     ((id, glue1) :: acc) *)
(*                 | None => acc *)
(*                 end) nil l. *)

(* Definition generate_drops (l: list composite_definition) (dropm: PTree.t ident) : PTree.t Clight.function := *)
(*   PTree_Properties.of_list (generate_drops_list l dropm). *)

Definition empty_drop := Clight.mkfunction Tvoid cc_default nil nil nil Clight.Sskip.

Definition generate_drops_acc (dropm: PTree.t ident) (id: ident) (co: composite) : Clight.function :=
  let glue := drop_glue_for_composite dropm id co.(co_sv) co.(co_members) in
  match glue with
  | Some glue1 => glue1
  | None => empty_drop
  end.
  
Definition generate_drops (dropm: PTree.t ident) : PTree.t Clight.function :=
  PTree.map (generate_drops_acc dropm) ce.

End COMPOSITE_ENV.


(** ** Step 3: Translate the Rust statement to Clight statement  *)

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  (* gen_next: ident; *)
  gen_trail: list (ident * Ctypes.type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), (* Ple (gen_next g) (gen_next g') -> *) result A g.


Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g.

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' => Res b g''
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Definition bind_res {A B: Type} (x: res A) (f: A -> mon B) : mon B :=
  fun g =>
    match x with
      | Error msg => Err msg
      | OK a =>
          match f a g with
          | Err msg => Err msg
          | Res b g' => Res b g'
      end
    end.

Definition bind_res2 {A B C: Type} (x: res (A * B)) (f: A -> B -> mon C) : mon C :=
  bind_res x (fun p => f (fst p) (snd p)).

Declare Scope gensym_monad_scope.
Notation "'dosym' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'dosym' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : gensym_monad_scope.
Notation "'docomb' X <- A ; B" := (bind_res A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'docomb' ( X , Y ) <- A ; B" := (bind_res2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : gensym_monad_scope.


Local Open Scope gensym_monad_scope.

Definition initial_generator : generator :=
  mkgenerator nil.

Definition gensym (ty: Ctypes.type): mon ident :=
  fun (g: generator) =>
    let fresh_id := fresh_atom tt in
    Res fresh_id
        (mkgenerator ((fresh_id, ty) :: gen_trail g)).
  

Definition get_variant_tag (ce: Ctypes.composite_env) (id:ident) : option ident :=
  match ce!id with
  | Some co =>
      match co.(co_su), co.(Ctypes.co_members) with
      | Ctypes.Struct, Ctypes.Member_plain tag type_int32s :: Ctypes.Member_plain body (Tunion _ noattr) :: nil =>
          Some tag
      | _, _ => None
      end
  | _ => None
  end.

Definition get_variant_body (ce: Ctypes.composite_env) (id:ident) : option ident :=
  match ce!id with
  | Some co =>
      match co.(co_su), co.(Ctypes.co_members) with
      | Ctypes.Struct, Ctypes.Member_plain tag type_int32s :: Ctypes.Member_plain body (Tunion _ noattr) :: nil =>
          Some body
      | _, _ => None
      end
  | _ => None
  end.


Section TRANSL.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.

Variable dropm: PTree.t ident.  (* map from composite id to its drop glue id *)

(** Error monad used in the translation of place and expression *)
Local Open Scope gensym_monad_scope.
Local Open Scope error_monad_scope.

Fixpoint place_to_cexpr (p: place) : res Clight.expr :=
  match p with
  | Plocal id ty =>      
      OK (Evar id (to_ctype ty))
  | Pfield p' fid ty =>   
    match typeof_place p' with
      | Tstruct _ id =>
        match ce!id with
        | Some co =>
            match co.(co_sv) with
            | Struct =>
              do e <- place_to_cexpr p';
              OK (Efield e fid (to_ctype ty))
            | _ => Error [CTX id; MSG ": it is not a correct struct"]
            end
        | _ => Error [CTX id; MSG ": Cannot find its composite in Rust composite environment : place_to_cexpr"]
        end
      | _ => Error (msg "Type error in Pfield: place_to_cexpr ")
      end
      
  | Pderef p' ty =>
    do e <- place_to_cexpr p';
    OK (Ederef e (to_ctype ty))
  | Pdowncast p fid ty =>
      (** FIXME: how to translate the get expression? *)
      match typeof_place p with
      | Tvariant _ id =>
          match ce!id, tce!id with
          | Some co, Some tco =>
              (** FIXME: the following code appears multiple times *)
              match co.(co_sv), tco.(Ctypes.co_members) with
              | TaggedUnion, Ctypes.Member_plain _ _ :: Ctypes.Member_plain union_id union_ty :: nil =>
                  (* pe.union_id.fid *)
                  do pe <- place_to_cexpr p;
                  OK (Efield (Efield pe union_id union_ty) fid (to_ctype ty))
              | _, _ => Error [CTX id; MSG ": it is not a correct tagged union"]
              end
          | _, _ => Error [CTX id; MSG ": Cannot find its composite in C composite environment : place_to_cexpr"]
          end
      | _ => Error (msg "Type error in Pdowncast: place_to_cexpr ")
      end
  end.
  

(* locals are used to check that global variables are disjoint with
locals to match the eval_Evar_global semantics in Clight *)
Fixpoint pexpr_to_cexpr (locals: list ident) (e: pexpr) : Errors.res Clight.expr :=
  match e with
  | Eunit => OK (Clight.Econst_int Int.zero Ctypes.type_int32s)
  | Econst_int i ty => OK (Clight.Econst_int i (to_ctype ty))
  | Econst_float f ty => OK (Clight.Econst_float f (to_ctype ty))
  | Econst_single f ty => OK (Clight.Econst_single f (to_ctype ty))
  | Econst_long l ty => OK (Clight.Econst_long l (to_ctype ty))
  (* just for compliation, we do not have semantics for it *)
  | Eglobal id ty =>
      if in_dec ident_eq id locals then
        Error ([CTX id; MSG " global variable is contained in locals "])
      else
        OK (Clight.Evar id (to_ctype ty))
  | Eplace p ty =>
      if type_eq_except_origins ty (typeof_place p) then        
        (place_to_cexpr p)
      else
        Error (msg "type error in Eplace (pexpr_to_cexpr)")
  | Eref _ _ p ty =>
      do e <- place_to_cexpr p;
      OK (Clight.Eaddrof e (to_ctype ty)) 
  | Ecktag p fid =>
      (** TODO: how to get the tagz from ctypes composite env? or still use Rust composite env? *)
      match typeof_place p with
      | Tvariant _ id =>
          match ce!id with
          | Some co =>
              match field_tag fid co.(co_members), get_variant_tag tce id with
              | Some tagz, Some tagid =>
                  do pe <- place_to_cexpr p;
                  OK (Clight.Ebinop Oeq (Clight.Efield pe tagid Ctypes.type_int32s) (Clight.Econst_int (Int.repr tagz) Ctypes.type_int32s) Ctypes.type_bool)
              | _, _ => Error (msg "Error in Ecktag 1: expr_to_cexpr")
              end
          | _ => Error (msg "Error in Ecktag 2: expr_to_cexpr")
          end
      | _ => Error (msg "Error in Ecktag 3, type error: expr_to_cexpr")
      end
  | Eunop uop e ty =>
      do e' <- pexpr_to_cexpr locals e;
      OK (Clight.Eunop uop e' (to_ctype ty))
  | Ebinop binop e1 e2 ty =>
      do e1' <- pexpr_to_cexpr locals e1;
      do e2' <- pexpr_to_cexpr locals e2;
      OK (Clight.Ebinop binop e1' e2' (to_ctype ty))
  end.

Definition expr_to_cexpr locals (e: expr) : res Clight.expr :=
  match e with
  | Emoveplace p ty =>
      pexpr_to_cexpr locals (Eplace p ty)
  | Epure pe =>
      pexpr_to_cexpr locals pe
  end.

Fixpoint expr_to_cexpr_list locals (l: list expr) : res (list Clight.expr) :=
  match l with
  | nil => OK nil
  | e :: l =>
      do e' <- expr_to_cexpr locals e;
      do l' <- expr_to_cexpr_list locals l;
      OK (e' :: l')
  end.

Definition transl_Sbox locals (temp: ident) (temp_ty: Ctypes.type) (deref_ty: Ctypes.type) (e: expr) : res (Clight.statement * Clight.expr) :=
  (* temp = malloc(sz);
     *temp = e;
     temp *)
  if complete_type ce (typeof e) then
    do e' <- expr_to_cexpr locals e;
    let e_ty := Clight.typeof e' in
    let sz := Ctypes.sizeof tce e_ty in
    (* check sz is in the range of ptrofs.max_unsigned which is used in
  proof *)
    if (0 <=? sz) && (sz <=? Ptrofs.max_unsigned) then
      let tempvar := Clight.Etempvar temp temp_ty in
      let malloc := (Evar malloc_id (Ctypes.Tfunction (Ctypes.Tcons Ctyping.size_t Ctypes.Tnil) (Tpointer Ctypes.Tvoid noattr) cc_default)) in
      let sz_expr := if Archi.ptr64
                     then Clight.Econst_long (Ptrofs.to_int64 (Ptrofs.repr sz)) Ctyping.size_t
                     else Clight.Econst_int (Ptrofs.to_int (Ptrofs.repr sz)) Ctyping.size_t in
      let call_malloc:= (Clight.Scall (Some temp) malloc (sz_expr :: nil)) in
      let assign_deref_temp := Clight.Sassign (Ederef tempvar deref_ty) e' in
      OK (Clight.Ssequence call_malloc assign_deref_temp, tempvar)
    else Error (msg "Size of type is not in range (transl_Sbox)")
  else Error (msg "malloc type is not complete (transl_Sbox)").

(* expand drop_in_place(temp), temp is a reference, ty is the type of
[*temp]. It is different from drop_glue_for_type because the expansion
is in the caller side. We need to use the reference to build the call
statement *)
Definition expand_drop (temp: ident) (ty: type) : option Clight.statement :=
  (* Use scalar type to simulate step_drop_scalar *)
  if negb (drop_type ty) then
  None
  else
  match ty with
  (* drop a box only drop the memory it points to, we do not care
  about the point-to type *)
  | Tbox ty' =>
      (* free(cty (deref temp)), deref temp has type [cty] and [deref
      temp] points to type [cty'] *)      
      let cty := to_ctype ty in
      let deref_temp := Ederef (Clight.Etempvar temp (Tpointer cty noattr)) cty in
      Some (call_free deref_temp)
  | Tstruct _ id 
  | Tvariant _ id  =>
      match dropm ! id with
      | None => None
      | Some id' =>
          (* temp has type [ref_cty] *)
          let ref_cty := Tpointer (to_ctype ty) noattr in
          let glue_ty := Ctypes.Tfunction (Ctypes.Tcons ref_cty Ctypes.Tnil) Tvoid cc_default in
          (* drop_in_place_xxx(temp) *)
          let call_stmt := Clight.Scall None (Evar id' glue_ty) ((Clight.Etempvar temp ref_cty) :: nil) in
          Some call_stmt
      end 
  | _ => None
  end.


Definition transl_assign_variant (p: place) (enum_id arm_id: ident) (e' lhs: Clight.expr) :=
  (* lhs.1 = tag;
         lhs.2. = e'; *)
  match ce!enum_id with
  | Some co =>
      match co.(co_sv) with
      | TaggedUnion =>          
          match field_tag arm_id co.(co_members), field_type arm_id co.(co_members) with
          (* an invariant: arm_id in co is the same as the field
              of type ty in generated union in C code *)
          | Some tagz, OK ty =>
              match tce!enum_id with
              | Some tco =>
                  match tco.(Ctypes.co_members) with
                  | Ctypes.Member_plain tag_id _ :: Ctypes.Member_plain body_id body_ty :: nil =>
                      match body_ty with
                      | Tunion union_id attr =>
                          let assign_tag := Clight.Sassign (Efield lhs tag_id Ctypes.type_int32s) (Clight.Econst_int (Int.repr tagz) Ctypes.type_int32s) in
                          let lhs' := (Efield (Efield lhs body_id (Tunion union_id attr)) arm_id (to_ctype ty)) in
                          let assign_body := Clight.Sassign lhs' e' in
                          (* We must first eval and store the value of expression and then store the tag because the tag in p may influence the value *)
                          OK (Clight.Ssequence assign_body assign_tag)
                      | _ => Error [CTX enum_id; MSG ": body type error when translating the variant assignement"]
                      end
                  | _ => Error [CTX enum_id; MSG ": cannot get its tag or body id when translating the variant assignement"]
                  end
              | _ => Error [CTX enum_id; MSG ": cannot get the composite definition from the composite environment in Rust or C"]
              end
          | _, _  => Error [CTX enum_id; MSG ": cannot get its tag value from the Rust composite environment"]
          end
      | _ => Error [CTX enum_id; MSG ": assign variant to a non-variant place"]
      end
  | _ => Error [CTX enum_id; MSG ": cannot get the composite definition from the composite environment in Rust or C"]
  end.


Fixpoint transl_stmt (locals: list ident) (stmt: statement) : mon Clight.statement :=
  let transl_stmt := transl_stmt locals in
  match stmt with
  | Sskip => ret Clight.Sskip
  | Sassign p e =>
      docomb e' <- expr_to_cexpr locals e;
      docomb lhs <- place_to_cexpr p;
      ret (Clight.Sassign lhs e')      
  | Sassign_variant p enum_id arm_id e =>
      docomb e' <- expr_to_cexpr locals e;
      docomb lhs <- place_to_cexpr p;
      (* let ty := typeof e in *)
      docomb r <- transl_assign_variant p enum_id arm_id e' lhs;
      ret r
  | Sbox p e =>
      (* temp = malloc(sizeof(e));
       *temp = e;
       p = temp *)
      let temp_ty := to_ctype (typeof_place p) in
      let deref_ty := to_ctype (deref_type (typeof_place p)) in
      dosym temp <- gensym temp_ty;
      docomb (stmt, e') <- transl_Sbox locals temp temp_ty deref_ty e;
      docomb pe <- place_to_cexpr p;
      ret (Clight.Ssequence stmt (Clight.Sassign pe e'))
  | Sstoragelive _
  | Sstoragedead _ =>
      ret (Clight.Ssequence Clight.Sskip Clight.Sskip)
  | Scall p e el =>
      docomb el' <- expr_to_cexpr_list locals el;
      docomb e' <- expr_to_cexpr locals e;
      docomb pe <- place_to_cexpr p;
      (** TODO: if p is a local, do not generate a new temp  *)
      (* temp = f();
         p = temp *)
      let ty := typeof_place p in
      let cty := to_ctype ty in
      dosym temp <- gensym cty;      
      let assign := Clight.Sassign pe (Etempvar temp cty) in
      ret (Clight.Ssequence (Clight.Scall (Some temp) e' el') assign)
  | Ssequence s1 s2 =>
      dosym s1' <- transl_stmt s1;
      dosym s2' <- transl_stmt s2;
      ret (Clight.Ssequence s1' s2')
  | Sifthenelse e s1 s2 =>
      docomb e' <- expr_to_cexpr locals e;
      dosym s1' <- transl_stmt s1;
      dosym s2' <- transl_stmt s2;
      ret (Clight.Sifthenelse e' s1' s2')
  | Sloop s =>
      dosym s' <- transl_stmt s;
      ret (Clight.Sloop s' Clight.Sskip)
  | Sbreak =>
      ret Clight.Sbreak
  | Scontinue =>
      ret Clight.Scontinue
  | Sreturn p =>
      docomb e' <- expr_to_cexpr locals (Epure (Eplace p (typeof_place p)));
      ret (Clight.Sreturn (Some e'))
  | Sdrop p =>
      (* drop(p) is expanded to
         temp = &p;
         drop_in_place(temp)
       *)
      let ty := (typeof_place p) in
      let cty := (to_ctype ty) in
      let ref_cty := Tpointer cty noattr in
      dosym temp <- gensym ref_cty;
      (* [temp=*p] *)
      docomb pe <- place_to_cexpr p;
      let set_stmt := Clight.Sset temp (Eaddrof pe ref_cty) in
      match expand_drop temp ty with
      | Some drop_stmt =>
          ret (Clight.Ssequence set_stmt drop_stmt)
      | None =>
          error (msg "Cannot find drop glue when expanding drop: build_stmt_until_extended_block")
      end
end.

(* empty Ctypes.composite_env *)

Definition empty_ce := PTree.empty Ctypes.composite.

Definition transl_function_normal (f: function) : Errors.res Clight.function :=
  let locals := var_names (f.(fn_params) ++ f.(fn_vars)) in
  match transl_stmt locals f.(fn_body) initial_generator with
  | Err msg => Errors.Error msg
  | Res stmt' g =>
      let params := map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) in
      let vars := map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) in
      (* check that temporaries are not repeated *)
      if list_norepet_dec ident_eq (Clight.var_names g.(gen_trail)) then
        if list_disjoint_dec ident_eq (var_names (f.(fn_params) ++ f.(fn_vars))) (malloc_id :: free_id :: (map snd (PTree.elements dropm))) then
          (** check the types of all the variables are complete. It
          should be changed if we want to support encapsulated
          type. *)
          if forallb (fun ty => complete_type ce ty) (map snd (f.(fn_params) ++ f.(fn_vars))) then
        (* update the next atom *)
          Errors.OK (Clight.mkfunction
                (to_ctype f.(fn_return))
                f.(fn_callconv)
                params
                vars
                g.(gen_trail)
                stmt')
          else
            Errors.Error [MSG "parameter and variable types are not complete"]
        else
          Errors.Error [MSG "parameter and variable names are not disjoint with drop id"]
        else
        Errors.Error [MSG "repeated temporary variables"]
  end.


(* step 3: translate a single function *)
Definition transl_function glues (f: function) : Errors.res Clight.function :=
  (* check whether this function is drop glue *)
  match f.(fn_drop_glue) with
  | Some comp_id =>
      match glues!comp_id with
      | Some glue =>
          Errors.OK glue
      | _ => Errors.Error [MSG "no drop glue for "; CTX comp_id; MSG " , it is invalid composite"]
      end
  | None => transl_function_normal f
  end.

Local Open Scope error_monad_scope.

Definition transl_fundef glues (_: ident) (fd: fundef) : Errors.res Clight.fundef :=
  (* Check if this fundef is drop glue *)
  match fd with
  | Internal f =>
      do tf <- transl_function glues f;
      Errors.OK (Ctypes.Internal tf)
  (* generate malloc *)
  | External orgs org_rels EF_malloc targs tres cconv =>
      OK malloc_decl
  | External orgs org_rels EF_free targs tres cconv =>
      OK free_decl
  | External orgs org_rels ef targs tres cconv =>
      OK (Ctypes.External ef (to_ctypelist targs) (to_ctype tres) cconv)
  end.

End TRANSL.

(* Check the existence of malloc and free *)

Definition check_malloc_free_existence (p: program) : bool :=
  match (prog_defmap p) ! malloc_id, (prog_defmap p) ! free_id with
  | Some (Gfun (External _ _ EF_malloc _ _ _)), Some (Gfun (External _ _ EF_free _ _ _)) =>
      true
  | _, _ => false
  end.

(* Translation of a whole program *)

Definition transl_globvar (id: ident) (ty: type) := OK (to_ctype ty).

Local Open Scope error_monad_scope.

Definition transl_program (p: program) : res Clight.program :=
  (* generate drop glue map: composite id to drop glue id *)
  let dropm := generate_dropm p in
  if list_disjoint_dec ident_eq [param_id] (malloc_id :: free_id :: (map snd (PTree.elements dropm))) then
    if check_malloc_free_existence p then
      if list_norepet_dec ident_eq (prog_defs_names p) then
      (* step 1: rust composite to c composite: generate union for each variant *)
        match transl_composites p.(prog_types) with
        | Some co_defs =>
            let tce := Ctypes.build_composite_env co_defs in
            (match tce as m return (tce = m) -> res Clight.program with
            | OK tce =>
                fun Hyp =>
                  let ce := p.(prog_comp_env) in
                  (* step 2: generate drop glue *)
                  let globs := generate_drops ce tce dropm in
                  (* step 3: translate the statement and convert drop glue *)
                  do p1 <- transform_partial_program2 (transl_fundef ce tce dropm globs) transl_globvar p;
                  OK {| Ctypes.prog_defs := AST.prog_defs p1;
                        Ctypes.prog_public := AST.prog_public p1;
                        Ctypes.prog_main := AST.prog_main p1;
                        Ctypes.prog_types := co_defs;
                        Ctypes.prog_comp_env := tce;
                        Ctypes.prog_comp_env_eq := Hyp |}
            | Error msg => fun _ => Error msg
            end) (eq_refl tce)
        | _ => Error (msg "error in transl_composites (Clightgen)")
        end
      else Error (msg "repeated function names (Clightgen)")
    else Error (msg "malloc/free does not exists (Clightgen)")
  else Error (msg "repeated drop glue paramter id (Clightgen)")
.
