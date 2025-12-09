Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST Errors.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepSafe.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import LanguageInterface.
Require Import Clight.
Require Import Rustlight Rustlightown RustIR.
Require Import InitDomain.
Require Import RustIRown StkBorPermission.

Import ListNotations.

(** ** Ownership based operational semantics for RustIR equipped with stacked borrow model (used for the soundness of borrow checking) *)

Section SEMANTICS.
          
(** States *)

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (e: env)
    (own: own_env)
    (sb: bor_stacks)            (* instrumented stacked borrow memory *)
    (m: mem) : state
| Callstate
    (vf: val)
    (args: list val)
    (k: cont)
    (sb: bor_stacks)
    (m: mem) : state
| Returnstate
    (res: val)
    (k: cont)
    (sb: bor_stacks)
    (m: mem) : state
(* Simulate elaborate drop *)
| Dropplace
    (f: function)
    (s: option drop_place_state)
    (l: list (place * bool))
    (k: cont)
    (e: env)
    (own: own_env)
    (sb: bor_stacks)
    (m: mem) : state
| Dropstate
(* The reason why dropstate does not contain the function is to match the new stack frame in Clight. *)
    (* composite name *)
    (c: ident)
    (v: val)
    (ds: option drop_member_state)
    (ms: members)
    (k: cont)
    (sb: bor_stacks)
    (m: mem): state.              


Local Open Scope error_monad_scope.

(** Deference a location based on the type  *)

Definition deref_loc_stkbor_access ce (ty: type) (sb: bor_stacks) (af: access_from) (b: block) (ofs: ptrofs) (ak: access_kind) : option bor_stacks :=
  memory_access sb b (Ptrofs.unsigned ofs) (sizeof ce ty) ak af.


(* What if ty is nested in some immutable reference? We should rule
out this situation in borrow checking, which should be significant to
maintain the invariant *)
Definition item_of_type (ty: type) (t: tag) : option item := 
  match ty with
  | Tbox _
  | Treference _ Mutable _ => Some (Unique t)
  | Treference _ Immutable _ => Some (SharedReadOnly t)
  | _ => None
  end.

Definition assign_loc_stkbor_access (ce: composite_env) (ty: type) (sb: bor_stacks) (b: block) (ofs: ptrofs) (af: access_from) (v: val) : option bor_stacks :=
  (* write access at (b, ofs) *)
  match memory_access sb b (Ptrofs.unsigned ofs) (sizeof ce ty) AccessWrite af with
  | Some sb1 =>
      (* if v is a pointer value point to the target location, we push
      (b, ofs) into the stack of the target location *)
      match v with
      | Vptr b1 ofs1 =>
          (* In our semantics, we do not provide who grant the access
          of this borrowing and just push the new tag onto the
          stack *)
          match item_of_type ty (b, (Ptrofs.unsigned ofs)) with
          | Some it =>
              grantN sb1 b1 (Ptrofs.unsigned ofs1) (Z.to_nat (sizeof ce (deref_type ty))) None it
          | None => None
          end
      | _ => Some sb1
      end
  | None => None
  end.

Inductive alloc_variables (ce: composite_env) : env -> mem -> bor_stacks ->
                                                list (ident * type) ->
                                                env -> mem -> bor_stacks -> Prop :=
| alloc_variables_nil:
  forall e m sb,
    alloc_variables ce e m sb nil e m sb
| alloc_variables_cons:
  forall e m id ty vars m1 b1 m2 e2 sb sb1 sb2,
    Mem.alloc m 0 (sizeof ce ty) = (m1, b1) ->
    init_stacks sb b1 0 (sizeof ce ty) = sb1 ->
    alloc_variables ce (PTree.set id (b1, ty) e) m1 sb1 vars e2 m2 sb2 ->
    alloc_variables ce e m sb ((id, ty) :: vars) e2 m2 sb2.

Inductive bind_parameters (ce: composite_env) (e: env):
                           mem -> bor_stacks -> list (ident * type) -> list val ->
                           mem -> bor_stacks -> Prop :=
  | bind_parameters_nil:
      forall m sb,
      bind_parameters ce e m sb nil nil m sb
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2 sb sb1 sb2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ce ty m b Ptrofs.zero v1 m1 ->
      assign_loc_stkbor_access ce ty sb b Ptrofs.zero from_local v1 = Some sb1 ->
      bind_parameters ce e m1 sb1 params vl m2 sb2 ->
      bind_parameters ce e m sb ((id, ty) :: params) (v1 :: vl) m2 sb2.

Inductive function_entry (ce: composite_env) (f: function) (vargs: list val) (m: mem) (sb: bor_stacks) (e: env) (m': mem) (sb': bor_stacks) : Prop :=
| function_entry_intro: forall m1 sb1,
    list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
    alloc_variables ce empty_env m sb (f.(fn_params) ++ f.(fn_vars)) e m1 sb1 ->
    bind_parameters ce e m1 sb1 f.(fn_params) vargs m' sb' ->
    function_entry ce f vargs m sb e m' sb'.

Fixpoint stkbor_free_list (sb: bor_stacks) (l: list (block * Z * Z)) : option bor_stacks :=
  match l with
  | nil => Some sb
  | (b, lo, hi) :: l' =>
      match memory_free sb b lo hi from_local with
      | None => None
      | Some sb' => stkbor_free_list sb' l'
      end
  end.

Section EXPR.

Variable ce: composite_env.
Variable e: env.
Variable m: mem.

(* Different from the eval_place in Rustlight/RustIR, we also return
the tag which denotes the permission granted for the access of the
returned location *)
Inductive eval_place (sb: bor_stacks) : place -> block -> ptrofs -> bor_stacks -> access_from -> Prop :=
| eval_Plocal: forall id b ty,
    e!id = Some (b, ty) ->
    eval_place sb (Plocal id ty) b Ptrofs.zero sb from_local
| eval_Pfield_struct: forall p ty b ofs delta id i co orgs bor_tag sb1,
    eval_place sb p b ofs sb1 bor_tag ->
    typeof_place p = Tstruct orgs id ->
    ce ! id = Some co ->
    field_offset ce i (co_members co) = OK delta ->
    eval_place sb (Pfield p i ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) sb1 bor_tag
| eval_Pdowncast: forall  p b ofs fofs id fid fty co orgs tag bor_tag sb1,
    eval_place sb p b ofs sb1 bor_tag ->
    typeof_place p = Tvariant orgs id ->
    ce ! id = Some co ->
    (* check tag and fid. If we want to remove this check, we need to
    show co_members are not repeated in MoveCheckingSafe to make sure
    wt_place and wt_footprint relate the same field ident. Without this checking, I don't know how to relate the (fid, fty) in footprint of bmatch and (fid, fty) in the place *)
    Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag) ->
    list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty) ->
    variant_field_offset ce fid (co_members co) = OK fofs ->
    (* fty and ty must be equal? *)
    eval_place sb (Pdowncast p fid fty) b (Ptrofs.add ofs (Ptrofs.repr fofs)) sb1 bor_tag
| eval_Pderef: forall p ty l ofs l' ofs' bor_tag sb1 sb2,
    eval_place sb p l ofs sb1 bor_tag ->
    deref_loc (typeof_place p) m l ofs (Vptr l' ofs') ->
    deref_loc_stkbor_access ce (typeof_place p) sb1 bor_tag l ofs AccessRead = Some sb2 ->
    (* As the value stored in *(l, ofs) is (Vptr l' ofs'), the granted
    tag for this location is (Tagged l ofs) *)
    eval_place sb (Pderef p ty) l' ofs' sb2 (from_ref (l, Ptrofs.unsigned ofs)).

Definition mut_to_access (mut: mutkind) : access_kind :=
  match mut with
  | Mutable => AccessWrite
  | Immutable => AccessRead
  end.

(* Evaluation of pure expression *)

Inductive eval_pexpr (se: Genv.symtbl) (sb: bor_stacks) : pexpr -> val -> bor_stacks -> Prop :=
| eval_Eunit:
    eval_pexpr se sb Eunit (Vint Int.zero) sb
| eval_Econst_int:   forall i ty,
    eval_pexpr se sb (Econst_int i ty) (Vint i) sb
| eval_Econst_float:   forall f ty,
    eval_pexpr se sb (Econst_float f ty) (Vfloat f) sb
| eval_Econst_single:   forall f ty,
    eval_pexpr se sb (Econst_single f ty) (Vsingle f) sb
| eval_Econst_long:   forall i ty,
    eval_pexpr se sb (Econst_long i ty) (Vlong i) sb
| eval_Eunop:  forall op a ty v1 v aty sb1,
    eval_pexpr se sb a v1 sb1 ->
    (* Note that to_ctype Tbox = None *)
    to_ctype (typeof_pexpr a) = aty ->
    (** TODO: define a rust-specific sem_unary_operation  *)
    sem_unary_operation op v1 aty m = Some v ->
    eval_pexpr se sb (Eunop op a ty) v sb1
| eval_Ebinop: forall op a1 a2 ty v1 v2 v ty1 ty2 sb1 sb2,
    eval_pexpr se sb a1 v1 sb1 ->
    eval_pexpr se sb1 a2 v2 sb2 ->
    to_ctype (typeof_pexpr a1) = ty1 ->
    to_ctype (typeof_pexpr a2) = ty2 ->
    sem_binary_operation_rust op v1 ty1 v2 ty2 m = Some v ->
    (* For now, we do not return moved place in binary operation *)
    eval_pexpr se sb (Ebinop op a1 a2 ty) v sb2
| eval_Eplace: forall p b ofs ty v bor_tag sb1 sb2,
    eval_place sb p b ofs sb1 bor_tag ->
    (* evaluate a place is considered as a read access of this place *)
    deref_loc ty m b ofs v ->
    deref_loc_stkbor_access ce (typeof_place p) sb1 bor_tag b ofs AccessRead = Some sb2 ->
    eval_pexpr se sb (Eplace p ty) v sb2
| eval_Ecktag: forall (p: place) b ofs tag tagz id fid co orgs bor_tag sb1 sb2
    (EVALP: eval_place sb p b ofs sb1 bor_tag)
    (* load the tag *) 
    (LOADTAG: Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag))
    (* One problem is that this read would make the borrow stack in
    tag and variance different. For now we consider it as a read on
    the whole enum *)
    (SBREAD: memory_read sb1 b (Ptrofs.unsigned ofs) (sizeof ce (typeof_place p)) bor_tag = Some sb2)
    (PTY: typeof_place p = Tvariant orgs id)
    (CO: ce ! id = Some co)
    (FTAG: field_tag fid co.(co_members) = Some tagz)
    (* adhoc: the range checking in the semantics is used to make sure
    that if the execution passes this check, the downcast evalution in
    the last match arms must be successful. Note that the last match
    arm is in the else statement. This checking is required for the
    soundness of eval_pexpr_error_sound *)   
    (RANGE: Int.unsigned tag < list_length_z co.(co_members)),
    eval_pexpr se sb (Ecktag p fid) (Val.of_bool (Int.eq tag (Int.repr tagz))) sb2
| eval_Eref: forall p b ofs mut ty org bor_tag sb1 sb2
    (EVALP: eval_place sb p b ofs sb1 bor_tag)
    (BORROW: match mut with
             | Mutable => memory_written sb1 b (Ptrofs.unsigned ofs) (sizeof ce ty) bor_tag
             | Immutable => memory_read sb1 b (Ptrofs.unsigned ofs) (sizeof ce ty) bor_tag
             end = Some sb2),
    eval_pexpr se sb (Eref org mut p ty) (Vptr b ofs) sb2
(* Evaluation of global variables which is used to support function
call *)
| eval_Eglobal: forall id ty b v
    (GADDR: Genv.find_symbol se id = Some b)
    (DEF: Rustlightown.deref_loc ty m b Ptrofs.zero v),
    eval_pexpr se sb (Eglobal id ty) v sb
.

      
(* expression evaluation has two phase: evaluate the value and produce
the moved-out place *)
Inductive eval_expr (se: Genv.symtbl) (sb: bor_stacks) : expr -> val -> bor_stacks -> Prop :=
| eval_Emoveplace: forall p ty b ofs v sb1 sb2 bor_tag,
    eval_place sb p b ofs sb1 bor_tag ->
    deref_loc ty m b ofs v ->
    (* move a place is considered as a write access of this place *)    
    deref_loc_stkbor_access ce (typeof_place p) sb1 bor_tag b ofs AccessWrite = Some sb2 ->
    eval_expr se sb (Emoveplace p ty) v sb2
| eval_Epure: forall pe v sb1,
    eval_pexpr se sb pe v sb1 ->
    eval_expr se sb (Epure pe) v sb1.

Inductive eval_exprlist se sb : list expr -> typelist -> list val -> bor_stacks -> Prop :=
| eval_Enil:
  eval_exprlist se sb nil Tnil nil sb
| eval_Econs:   forall a bl ty tyl v1 v2 vl sb1 sb2,
    eval_expr se sb a v1 sb1 ->
    sem_cast v1 (typeof a) ty = Some v2 ->
    eval_exprlist se sb1 bl tyl vl sb2 ->
    eval_exprlist se sb (a :: bl) (Tcons ty tyl) (v2 :: vl) sb2.

End EXPR.


Section SMALLSTEP.

Variable ge: genv.

(* It is mostly the same as that in RustIRown. We do not update borrow
stack in this drop semantics because we think it is not beneficial in
alias analysis. If we read the value pointed by some freed block, it
is already UB. *)
Inductive step_drop : state -> trace -> state -> Prop :=
| step_dropstate_init: forall id b ofs fid fty membs k sb m,
    step_drop (Dropstate id (Vptr b ofs) None ((Member_plain fid fty) :: membs) k sb m) E0 (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) membs k sb m)
| step_dropstate_struct: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys sb m k membs fid fty fofs orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (STRUCT: co2.(co_sv) = Struct),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k sb m) E0
      (Dropstate id2 (Vptr cb cofs) None co2.(co_members) (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid fty tys)) membs k) sb m)
| step_dropstate_enum: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys sb m k membs fid1 fty1 fid2 fty2 fofs tag orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (ENUM: co2.(co_sv) = TaggedUnion)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr cb cofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co2.(co_members) (Int.unsigned tag) = Some (Member_plain fid2 fty2)),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k sb m) E0
      (Dropstate id2 (Vptr cb cofs) (type_to_drop_member_state ge fid2 fty2) nil (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid1 fty1 tys)) membs k) sb m)
| step_dropstate_box: forall b ofs id co fid fofs m m' tys k membs fty sb
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (DROPB: drop_box_rec ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys m'),
    step_drop
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k sb m) E0
      (Dropstate id (Vptr b ofs) None membs k sb m')
| step_dropstate_return1: forall b ofs id m f e own k ps s sb,
    step_drop
      (* maybe we should separate step_dropstate_return to reuse
      step_drop because of the mismatch between Kdropplace and Kcall
      in RustIRown and RUstIRsem *)
      (Dropstate id (Vptr b ofs) None nil (Kdropplace f s ps e own k) sb m) E0
      (Dropplace f s ps k e own sb m)
| step_dropstate_return2: forall b1 b2 ofs1 ofs2 id1 id2 m k membs s sb,
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) None nil (Kdropcall id2 (Vptr b2 ofs2) s membs k) sb m) E0
      (Dropstate id2 (Vptr b2 ofs2) s membs k sb m)
.

(* The procedure of dropping a place: we first check its intiialization status (is_init): 1. if false, skip this place; 2. if true, we then check if it is scalar type. 2.1. if true, update the own_env and then skip this place; 2.2 if false, start to drop this place *)

Inductive step_dropplace : state -> trace -> state -> Prop :=
| step_dropplace_init1: forall f p ps k le own sb m full
    (* p is not owned, so just skip it (How to relate this case with
    RustIRsem because drop elaboration removes this place earlier in
    generate_drop_flag) *)
    (NOTOWN: is_init own p = false),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own sb m) E0
      (Dropplace f None ps k le own sb m)
| step_dropplace_init2: forall f p ps k le own sb m st (full: bool)
    (OWN: is_init own p = true)
    (NOTSCALAR: scalar_type (typeof_place p) = false)
    (DPLACE: st = (if full then gen_drop_place_state p else drop_fully_owned_box [p])),
    (* move p to match drop p *)
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own sb m) E0
      (Dropplace f (Some st) ps k le (move_place own p) sb m)
| step_dropplace_scalar: forall f p ps k le own m full sb
    (OWN: is_init own p = true)
    (SCALAR: scalar_type (typeof_place p) = true),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own sb m) E0
      (Dropplace f None ps k le (move_place own p) sb m)

| step_dropplace_box: forall le m m' k ty b' ofs' f b ofs p own ps l sb
    (* simulate step_drop_box in RustIRsem *)
    (PADDR: Rustlightown.eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: Rustlightown.deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* Simulate free semantics *)
    (FREE: extcall_free_sem ge [Vptr b' ofs'] m E0 Vundef m'),
    (* We are dropping p. fp is the fully owned place which is split into p::l *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own sb m) E0
      (Dropplace f (Some (drop_fully_owned_box l)) ps k le own sb m')
| step_dropplace_struct: forall m k orgs co id p b ofs f le own ps l sb
    (* It corresponds to the call step to the drop glue of this struct *)
    (PTY: typeof_place p = Tstruct orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COSTRUCT: co.(co_sv) = Struct)
    (PADDR: Rustlightown.eval_place ge le m p b ofs),
    (* update the ownership environment in continuation *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own sb m) E0
      (Dropstate id (Vptr b ofs) None co.(co_members) (Kdropplace f (Some (drop_fully_owned_box l)) ps le own k) sb m)
| step_dropplace_enum: forall m k p orgs co id fid fty tag b ofs f le own ps l sb
    (PTY: typeof_place p = Tvariant orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COENUM: co.(co_sv) = TaggedUnion)
    (PADDR: Rustlightown.eval_place ge le m p b ofs)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty)),
    (* update the ownership environment in continuation *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own sb m) E0
      (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) nil (Kdropplace f (Some (drop_fully_owned_box l)) ps le own k) sb m)
| step_dropplace_next: forall f ps k le own m sb,
    step_dropplace (Dropplace f (Some (drop_fully_owned_box nil)) ps k le own sb m) E0
      (Dropplace f None ps k le own sb m)
| step_dropplace_return: forall f k le own m sb,
    step_dropplace (Dropplace f None nil k le own sb m) E0
      (State f Sskip k le own sb m)
.

Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e p k le m1 m2 b ofs v v1 own1 own2 own3 sb1 sb2 sb3 sb4 bor_tag
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3)
    (TYP: forall orgs id, typeof_place p <> Tvariant orgs id),
    (* evaluate the expr, return the value *)
    eval_expr ge le m1 ge sb1 e v sb2 ->
    (* sem_cast to simulate Clight *)
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    (* get the location of the place *)
    eval_place ge le m1 sb2 p b ofs sb3 bor_tag ->
    (* assign to p *)
    assign_loc ge (typeof_place p) m1 b ofs v1 m2 ->
    (* update borrow stack according to the assign_loc *)
    assign_loc_stkbor_access ge (typeof_place p) sb3 b ofs bor_tag v1 = Some sb4 ->
    step (State f (Sassign p e) k le own1 sb1 m1) E0 (State f Sskip k le own3 sb4 m2)
| step_assign_variant: forall f e p ty k le m1 m2 m3 b ofs b1 ofs1 v v1 tag co fid enum_id orgs own1 own2 own3 fofs sb1 sb2 sb3 sb4 sb5 sb6 bor_tag1 bor_tag2
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3)
    (* necessary for clightgen simulation *)
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (* evaluate the expr, return the value *)
    (EXPR: eval_expr ge le m1 ge sb1 e v sb2)
    (* evaluate the location of the variant in p (in memory m1) *)
    (PADDR1: eval_place ge le m1 sb2 p b ofs sb3 bor_tag1)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (* sem_cast to simulate Clight *)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (* set the value *)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (ASBOR: assign_loc_stkbor_access ge ty sb3 b (Ptrofs.add ofs (Ptrofs.repr fofs)) bor_tag1 v1 = Some sb4)
    (** different from normal assignment: update the tag and assign value *)
    (TAG: field_tag fid co.(co_members) = Some tag)
    (* eval the location of the tag: to simulate the target statement:
    because we cannot guarantee that store value in m1 does not change
    the address of p! (Non-interference is a difficult problem!) *)
    (PADDR2: eval_place ge le m2 sb4 p b1 ofs1 sb5 bor_tag2)
    (* set the tag *)
    (STAG: Mem.storev Mint32 m2 (Vptr b1 ofs1) (Vint (Int.repr tag)) = Some m3)
    (STAGBOR: memory_access sb5 b1 (Ptrofs.unsigned ofs1) (size_chunk Mint32) AccessWrite bor_tag2 = Some sb6),
   step (State f (Sassign_variant p enum_id fid e) k le own1 sb1 m1) E0 (State f Sskip k le own3 sb6 m3)
| step_box: forall f e p ty k le m1 m2 m3 m4 m5 b v v1 pb pofs own1 own2 own3 sb1 sb2 sb3 sb4 sb5 bor_tag
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3)
    (TYP: typeof_place p = Tbox ty)
    (* Simulate malloc semantics to allocate the memory block *)
    (ALLOC: Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b))
    (INITSTK: init_stacks sb1 b 0 (sizeof ge (typeof e)) = sb2)
    (STORESZ: Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3)
    (* evaluate the expression after malloc to simulate*)
    (EXPR: eval_expr ge le m3 ge sb2 e v sb3)
    (* sem_cast the value to simulate function call in Clight *)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (* assign the value to the allocated location. No need to access
    the borrow stack of this new allocated locaiton *)
    (AS: assign_loc ge ty m3 b Ptrofs.zero v1 m4)
    (* assign the address to p *)
    (EVALP: eval_place ge le m4 sb3 p pb pofs sb4 bor_tag)
    (ASP: assign_loc ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) m5)
    (ASPBOR: assign_loc_stkbor_access ge (typeof_place p) sb4 pb pofs bor_tag (Vptr b Ptrofs.zero) = Some sb5),
    step (State f (Sbox p e) k le own1 sb1 m1) E0 (State f Sskip k le own3 sb5 m5)

(** dynamic drop semantics: simulate the drop elaboration *)
| step_to_dropplace: forall f p le own sb m drops k universe
    (UNI: PathsMap.get (local_of_place p) own.(own_universe) = universe)
    (SPLIT: split_drop_place ge universe p (typeof_place p) = OK drops),
    (* get the owned place to drop *)
    step (State f (Sdrop p) k le own sb m) E0
      (Dropplace f None drops k le own sb m)
| step_in_dropplace: forall f s ps k le own sb m E S
    (SDROP: step_dropplace (Dropplace f s ps k le own sb m) E S),
    step (Dropplace f s ps k le own sb m) E S
| step_dropstate: forall id v s membs k sb m S E
    (SDROP: step_drop (Dropstate id v s membs k sb m) E S),
    step (Dropstate id v s membs k sb m) E S
    
| step_storagelive: forall f k le sb m id own,
    step (State f (Sstoragelive id) k le own sb m) E0 (State f Sskip k le own sb m)
| step_storagedead: forall f k le m id own ty b sb1 sb2,
    (* In Miri, storagedead is considered as a deallocation of this local *)
    le ! id = Some (b, ty) ->    (* We should check that this id must be a local variable *)
    memory_free sb1 b 0 (sizeof ge ty) from_local = Some sb2 ->
    step (State f (Sstoragedead id) k le own sb1 m) E0 (State f Sskip k le own sb2 m)
         
| step_call: forall f a al k le m vargs tyargs vf fd cconv tyres p orgs org_rels own1 own2 sb1 sb2 sb3
    (TFEXPRLIST: move_place_list own1 (moved_place_list al) = own2)
    (GFUN: function_not_drop_glue fd),
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge le m ge sb1 a vf sb2 ->
    eval_exprlist ge le m ge sb2 al tyargs vargs sb3 ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    step (State f (Scall p a al) k le own1 sb1 m) E0 (Callstate vf vargs (Kcall p f le own2 k) sb3 m)

| step_internal_function: forall vf f vargs k m e m' own1 own2 sb sb'
    (FIND: Genv.find_funct ge vf = Some (Internal f))
    (NORMAL: f.(fn_drop_glue) = None)
    (* initialize own_env *)
    (INITOWN: init_own_env ge f = OK own1)
    (INITPARAMS: init_place_list own1 (places_of_locals f.(fn_params)) = own2)
    (ENTRY: function_entry ge f vargs m sb e m' sb'),
    step (Callstate vf vargs k sb m) E0 (State f f.(fn_body) k e own2 sb' m')

| step_external_function: forall vf vargs k m m' cc ty typs ef v t orgs org_rels sb
    (FIND: Genv.find_funct ge vf = Some (External orgs org_rels ef typs ty cc))
    (NORMAL: ef <> EF_malloc /\ ef <> EF_free),
    external_call ef ge vargs m t v m' ->
    step (Callstate vf vargs k sb m) t (Returnstate v k sb m')

(** Return cases. For the reason why we do not support return None and
skip return, see Rustlightown.v *)
(* | step_return_0: forall e lb m1 m2 f k own, *)
(*     blocks_of_env ge e = lb -> *)
(*     (* drop the stack blocks *) *)
(*     Mem.free_list m1 lb = Some m2 -> *)
(*     (* return unit or Vundef? *) *)
(*     step (State f (Sreturn None) k e own m1) E0 (Returnstate Vundef (call_cont k) m2) *)
| step_return_1: forall le p v v1 lb m1 m2 f k ck own1 sb1 sb2
    (CONT: call_cont k = Some ck)
    (* (TFEXPR: move_place_option own1 (moved_place a) = own2), *)
    (EVAL: eval_expr ge le m1 ge sb1 (Epure (Eplace p (typeof_place p))) v sb2)
    (* sem_cast to the return type *)
    (CAST: sem_cast v (typeof_place p) f.(fn_return) = Some v1)
    (* drop the stack blocks *)
    (STK: blocks_of_env ge le = lb)
    (FREE: Mem.free_list m1 lb = Some m2)
    (BORFREE: stkbor_free_list sb1 lb = Some sb2),
    step (State f (Sreturn p) k le own1 sb1 m1) E0 (Returnstate v1 ck sb2 m2)
(* no return statement but reach the end of the function *)
(* | step_skip_call: forall e lb m1 m2 f k own, *)
(*     is_call_cont k -> *)
(*     blocks_of_env ge e = lb -> *)
(*     Mem.free_list m1 lb = Some m2 -> *)
(*     step (State f Sskip k e own m1) E0 (Returnstate Vundef (call_cont k) m2) *)

| step_returnstate: forall p v b ofs m1 m2 e f k own1 own2 sb1 sb2 sb3 bor_tag
    (TFASSIGN: own_transfer_assign own1 p = own2),
    eval_place ge e m1 sb1 p b ofs sb2 bor_tag ->
    val_casted v (typeof_place p) ->
    assign_loc ge (typeof_place p) m1 b ofs v m2 ->    
    assign_loc_stkbor_access ge (typeof_place p) sb2 b ofs bor_tag v = Some sb3 ->
    step (Returnstate v (Kcall p f e own1 k) sb1 m1) E0 (State f Sskip k e own2 sb3 m2)

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e m own sb,
    step (State f (Ssequence s1 s2) k e own sb m)
      E0 (State f s1 (Kseq s2 k) e own sb m)
| step_skip_seq: forall f s k e m own sb,
    step (State f Sskip (Kseq s k) e own sb m)
      E0 (State f s k e own sb m)
| step_continue_seq: forall f s k e m own sb,
    step (State f Scontinue (Kseq s k) e own sb m)
      E0 (State f Scontinue k e own sb m)
| step_break_seq: forall f s k e m own sb,
    step (State f Sbreak (Kseq s k) e own sb m)
      E0 (State f Sbreak k e own sb m)
| step_ifthenelse:  forall f a s1 s2 k e m v1 b ty own1 sb1 sb2,
    (* there is no receiver for the moved place, so it must be None *)
    eval_expr ge e m ge sb1 a v1 sb2 ->
    to_ctype (typeof a) = ty ->
    bool_val v1 ty m = Some b ->
    step (State f (Sifthenelse a s1 s2) k e own1 sb1 m)
      E0 (State f (if b then s1 else s2) k e own1 sb2 m)
| step_loop: forall f s k e m own sb,
    step (State f (Sloop s) k e own sb m)
      E0 (State f s (Kloop s k) e own sb m)
| step_skip_or_continue_loop:  forall f s k e m x own sb,
    x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop s k) e own sb m)
      E0 (State f s (Kloop s k) e own sb m)
| step_break_loop:  forall f s k e m own sb,
    step (State f Sbreak (Kloop s k) e own sb m)
      E0 (State f Sskip k e own sb m)
.


(** Open semantics *)

Record rust_stkbor_query :=
  rsbor_q {
    rsq_q :> rust_query;
    (* rsq_vf: val; *)
    (* rsq_sg: rust_signature; *)
    (* rsq_args: list val; *)
    (* rsq_mem: mem; *)
    rsq_stk: bor_stacks;
  }.

Record rust_stkbor_reply :=
  rsbor_r {
    rsr_r :> rust_reply;
    (* rsr_retval: val; *)
    (* rsr_mem: mem; *)
    rsr_stk: bor_stacks;
  }.

Definition li_rs_bor : language_interface :=
  {|
    query := rust_stkbor_query;
    reply := rust_stkbor_reply;
    entry := rsq_vf;
  |}.


Inductive initial_state: (query li_rs_bor) -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc vargs m orgs org_rels sb,
    Genv.find_funct ge vf = Some (Internal f) ->
    type_of_function f = Tfunction orgs org_rels targs tres tcc ->
    (* This function must not be drop glue *)
    f.(fn_drop_glue) = None ->
    (* how to use it? *)
    val_casted_list vargs targs ->
    (* Mem.sup_include (Genv.genv_sup ge) (Mem.support m) -> *)
    initial_state (rsbor_q (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge) vargs m) sb)
      (Callstate vf vargs Kstop sb m).
    
Inductive at_external: state -> (query li_rs_bor) -> Prop:=
| at_external_intro: forall vf name args k m targs tres cconv orgs org_rels sb,
    Genv.find_funct ge vf = Some (External orgs org_rels (EF_external name (signature_of_type targs tres cconv)) targs tres cconv) ->
    at_external (Callstate vf args k sb m) (rsbor_q (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres cconv ge) args m) sb).

Inductive after_external: state -> (reply li_rs_bor) -> state -> Prop:=
| after_external_intro: forall vf args k m m' v sb sb',
    after_external
      (Callstate vf args k sb m)
      (rsbor_r (rsr v m') sb')
      (Returnstate v k sb' m').

Inductive final_state: state -> (reply li_rs_bor) -> Prop:=
| final_state_intro: forall v m sb,
    final_state (Returnstate v Kstop sb m) (rsbor_r (rsr v m) sb).

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.
