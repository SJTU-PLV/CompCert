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
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import LanguageInterface.
Require Import Clight.
Require Import Rustlight Rustlightown RustIR.
Require Import InitDomain.

Import ListNotations.

(** ** Operational semantics for RustIR (the semantics after drop elaboration without ownership local environment) *)

Section SEMANTICS.

(** Continuation *)
  
Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Kloop: statement -> cont -> cont
| Kcall: option place -> function -> env -> cont -> cont
| Kdropcall: ident -> val -> option drop_member_state -> members -> cont -> cont
.

(** Pop continuation until a call or stop *)

(* Return from dropstate is UB *)
Fixpoint call_cont (k: cont) : option cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop s k => call_cont k
  | Kdropcall _ _ _ _ _ => None
  (* Adhoc: Kcall None represents calling drop glue. This should be replaced by a new cont *)
  | Kcall None _ _ k => None
  | _ => Some k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ => True
  | _ => False
  end.

(** States *)

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (e: env)
    (m: mem) : state
| Callstate
    (vf: val)
    (args: list val)
    (k: cont)
    (m: mem) : state
| Returnstate
    (res: val)
    (k: cont)
    (m: mem) : state
(* | Calldrop *)
(*     (* It is necessary for reducing the number of states transition *) *)
(*     (v: val) *)
(*     (ty: type) *)
(*     (k: cont)   *)
(*     (m: mem): state *)
| Dropstate
    (* composite name *)
    (c: ident)
    (v: val)
    (ds: option drop_member_state)
    (ms: members)
    (k: cont)
    (m: mem): state.

Section SMALLSTEP.

Variable ge: genv.

Inductive step_drop : state -> trace -> state -> Prop :=
| step_dropstate_init: forall id b ofs fid fty membs k m,
    step_drop (Dropstate id (Vptr b ofs) None ((Member_plain fid fty) :: membs) k m) E0 (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) membs k m)
| step_dropstate_struct: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid fty fofs  orgs
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
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) None co2.(co_members) (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid fty tys)) membs k) m)
| step_dropstate_enum: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fid2 fty2 fofs tag orgs
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
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) (type_to_drop_member_state ge fid2 fty2) nil (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid1 fty1 tys)) membs k) m)
| step_dropstate_box: forall b ofs id co fid fofs m m' tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (DROPB: drop_box_rec ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys m'),
    step_drop
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m) E0
      (Dropstate id (Vptr b ofs) None membs k m')
| step_dropstate_return1: forall b ofs id m f e k,
    step_drop
      (Dropstate id (Vptr b ofs) None nil (Kcall None f e k) m) E0
      (State f Sskip k e m)
| step_dropstate_return2: forall b1 b2 ofs1 ofs2 id1 id2 m k membs s,
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) None nil (Kdropcall id2 (Vptr b2 ofs2) s membs k) m) E0
      (Dropstate id2 (Vptr b2 ofs2) s membs k m)
.


Inductive step_drop_mem_error : state -> Prop :=
| step_dropstate_struct_error: forall id1 id2 co1 b1 ofs1 tys m k membs fid fty fofs orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK fofs)
    (* error in loading the address of the composite *)
    (DEREF: deref_loc_rec_mem_error m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys),
    step_drop_mem_error
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m)
| step_dropstate_enum_error1: forall id1 id2 co1 b1 ofs1 tys m k membs fid1 fty1 fofs orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* error in loading the address of the composite *)
    (DEREF: deref_loc_rec_mem_error m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys),
    step_drop_mem_error
    (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m)
| step_dropstate_enum_error2: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fofs orgs
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
    (* error in loading the tag *)
    (TAG: ~ Mem.valid_access m Mint32 cb (Ptrofs.unsigned cofs) Readable),
    step_drop_mem_error
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m)      
| step_dropstate_box_error: forall b ofs id co fid fofs m tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (* error in dropping the box chain *)
    (DROPB: drop_box_rec_mem_error ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys),
    step_drop_mem_error
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m)
.


Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e p k le m1 m2 b ofs v v1,
    (* get the location of the place *)
    eval_place ge le m1 p b ofs ->
    (* evaluate the expr, return the value *)
    eval_expr ge le m1 ge e v ->
    (* sem_cast to simulate Clight *)
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    (* assign to p *)
    assign_loc ge (typeof_place p) m1 b ofs v1 m2 ->
    step (State f (Sassign p e) k le m1) E0 (State f Sskip k le m2)
| step_assign_variant: forall f e p ty k le m1 m2 m3 b ofs b1 ofs1 v v1 tag co fid enum_id orgs fofs
    (* necessary for clightgen simulation *)
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (* evaluate the expr, return the value *)
    (EXPR: eval_expr ge le m1 ge e v)
    (* evaluate the location of the variant in p (in memory m1) *)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (* sem_cast to simulate Clight *)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (* set the value *)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (** different from normal assignment: update the tag and assign value *)
    (TAG: field_tag fid co.(co_members) = Some tag)
    (* eval the location of the tag: to simulate the target statement:
    because we cannot guarantee that store value in m1 does not change
    the address of p! (Non-interference is a difficult problem!) *)
    (PADDR2: eval_place ge le m2 p b1 ofs1)
    (* set the tag *)
    (STAG: Mem.storev Mint32 m2 (Vptr b1 ofs1) (Vint (Int.repr tag)) = Some m3),
    (* variant_field_offset ge fid co.(co_members) = OK (ofs', bf) ->- *)
    step (State f (Sassign_variant p enum_id fid e) k le m1) E0 (State f Sskip k le m3)
| step_box: forall f e p ty k le m1 m2 m3 m4 m5 b v v1 pb pofs,
    typeof_place p = Tbox ty ->
    (* Simulate malloc semantics to allocate the memory block *)
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    (* evaluate the expression after malloc to simulate*)
    eval_expr ge le m3 ge e v ->
    (* sem_cast the value to simulate function call in Clight *)
    sem_cast v (typeof e) ty = Some v1 ->
    (* assign the value to the allocated location *)
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    (* assign the address to p *)
    eval_place ge le m4 p pb pofs ->
    assign_loc ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) m5 ->
    step (State f (Sbox p e) k le m1) E0 (State f Sskip k le m5)

(** Small-step drop semantics *)
| step_drop_box: forall le m m' k ty b' ofs' f b ofs p
    (* We assume that drop(p) where p is box type has been expanded in
    drop elaboration (see drop_fully_own in ElaborateDrop.v) *)
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* Simulate free semantics *)
    (FREE: extcall_free_sem ge [Vptr b' ofs'] m E0 Vundef m'),
    step (State f (Sdrop p) k le m) E0 (State f Sskip k le m')
| step_drop_struct: forall m k orgs co id p b ofs f le
    (* It corresponds to the call step to the drop glue of this struct *)
    (PTY: typeof_place p = Tstruct orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COSTRUCT: co.(co_sv) = Struct)
    (PADDR: eval_place ge le m p b ofs),
    step
      (State f (Sdrop p) k le m) E0
      (Dropstate id (Vptr b ofs) None co.(co_members) (Kcall None f le k) m)
| step_drop_enum: forall m k p orgs co id fid fty tag b ofs f le
    (PTY: typeof_place p = Tvariant orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COENUM: co.(co_sv) = TaggedUnion)
    (PADDR: eval_place ge le m p b ofs)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty)),
    step
    (State f (Sdrop p) k le m) E0
    (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) nil (Kcall None f le k) m)
| step_dropstate: forall id v s membs k m S E
    (SDROP: step_drop (Dropstate id v s membs k m) E S),
    step (Dropstate id v s membs k m) E S
    
| step_storagelive: forall f k le m id,
    step (State f (Sstoragelive id) k le m) E0 (State f Sskip k le m)
| step_storagedead: forall f k le m id,
    step (State f (Sstoragedead id) k le m) E0 (State f Sskip k le m)
| step_call: forall f a al k le m vargs tyargs vf fd cconv tyres p orgs org_rels,    
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge le m ge a vf ->
    eval_exprlist ge le m ge al tyargs vargs ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    function_not_drop_glue fd ->
    step (State f (Scall p a al) k le m) E0 (Callstate vf vargs (Kcall (Some p) f le k) m)

| step_internal_function: forall vf f vargs k m e m'
    (FIND: Genv.find_funct ge vf = Some (Internal f))
    (NORMAL: f.(fn_drop_glue) = None),
    function_entry ge f vargs m e m' ->
    step (Callstate vf vargs k m) E0 (State f f.(fn_body) k e m')

| step_external_function: forall vf vargs k m m' cc ty typs ef v t orgs org_rels
    (FIND: Genv.find_funct ge vf = Some (External orgs org_rels ef typs ty cc))
    (NORMAL: ef <> EF_malloc /\ ef <> EF_free),
    external_call ef ge vargs m t v m' ->
    step (Callstate vf vargs k m) t (Returnstate v k m')
   
(** Return cases *)
(* | step_return_0: forall e lb m1 m2 f k, *)
(*     (forall id b t, e ! id = Some (b, t) -> complete_type ge t = true) -> *)
(*     blocks_of_env ge e = lb -> *)
(*     (* drop the stack blocks *) *)
(*     Mem.free_list m1 lb = Some m2 -> *)
(*     (* return unit or Vundef? *) *)
(*     step (State f (Sreturn None) k e m1) E0 (Returnstate Vundef (call_cont k) m2) *)
| step_return_1: forall le p v v1 lb m1 m2 f k ck
    (CONT: call_cont k = Some ck),
    eval_expr ge le m1 ge (Epure (Eplace p (typeof_place p))) v ->
    (** check it in Clightgen *)
    (* (forall id b t, le ! id = Some (b, t) -> complete_type ge t = true) -> *)
    (* sem_cast to the return type *)
    sem_cast v (typeof_place p) f.(fn_return) = Some v1 ->
    (* drop the stack blocks *)
    blocks_of_env ge le = lb ->
    Mem.free_list m1 lb = Some m2 ->
    step (State f (Sreturn p) k le m1) E0 (Returnstate v1 ck m2)
(* no return statement but reach the end of the function *)
(* | step_skip_call: forall e lb m1 m2 f k, *)
(*     is_call_cont k -> *)
(*     (forall id b t, e ! id = Some (b, t) -> complete_type ge t = true) -> *)
(*     blocks_of_env ge e = lb -> *)
(*     Mem.free_list m1 lb = Some m2 -> *)
(*     step (State f Sskip k e m1) E0 (Returnstate Vundef (call_cont k) m2) *)
         
| step_returnstate: forall p v b ofs m1 m2 e f k,
    eval_place ge e m1 p b ofs ->
    val_casted v (typeof_place p)->
    assign_loc ge (typeof_place p) m1 b ofs v m2 ->     
    step (Returnstate v (Kcall (Some p) f e k) m1) E0 (State f Sskip k e m2)

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e m,
    step (State f (Ssequence s1 s2) k e m)
      E0 (State f s1 (Kseq s2 k) e m)
| step_skip_seq: forall f s k e m,
    step (State f Sskip (Kseq s k) e m)
      E0 (State f s k e m)
| step_continue_seq: forall f s k e m,
    step (State f Scontinue (Kseq s k) e m)
      E0 (State f Scontinue k e m)
| step_break_seq: forall f s k e m,
    step (State f Sbreak (Kseq s k) e m)
      E0 (State f Sbreak k e m)
| step_ifthenelse:  forall f a s1 s2 k e m v1 b ty,
    (* there is no receiver for the moved place, so it must be None *)
    eval_expr ge e m ge a v1 ->
    to_ctype (typeof a) = ty ->
    bool_val v1 ty m = Some b ->
    step (State f (Sifthenelse a s1 s2) k e m)
      E0 (State f (if b then s1 else s2) k e m)
| step_loop: forall f s k e m,
    step (State f (Sloop s) k e m)
      E0 (State f s (Kloop s k) e m)
| step_skip_or_continue_loop:  forall f s k e m x,
    x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop s k) e m)
      E0 (State f s (Kloop s k) e m)
| step_break_loop:  forall f s k e m,
    step (State f Sbreak (Kloop s k) e m)
      E0 (State f Sskip k e m)
.


(** Open semantics *)

Inductive initial_state: rust_query -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc vargs m orgs org_rels,
    Genv.find_funct ge vf = Some (Internal f) ->
    type_of_function f = Tfunction orgs org_rels targs tres tcc ->
    (* This function must not be drop glue *)
    f.(fn_drop_glue) = None ->
    (* how to use it? *)
    val_casted_list vargs targs ->
    (* Mem.sup_include (Genv.genv_sup ge) (Mem.support m) -> *)
    initial_state (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge) vargs m)
      (Callstate vf vargs Kstop m).


Inductive at_external: state -> rust_query -> Prop:=
| at_external_intro: forall vf name args k m targs tres cconv orgs org_rels,
    (* check the validity of the signature *)
    Genv.find_funct ge vf = Some (External orgs org_rels (EF_external name (signature_of_type targs tres cconv)) targs tres cconv) ->
    at_external (Callstate vf args k m) (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres cconv ge) args m).

Inductive after_external: state -> rust_reply -> state -> Prop:=
| after_external_intro: forall vf args k m m' v,
    after_external
      (Callstate vf args k m)
      (rsr v m')
      (Returnstate v k m').

Inductive final_state: state -> rust_reply -> Prop:=
| final_state_intro: forall v m,
    final_state (Returnstate v Kstop m) (rsr v m).

(* Definition of memory error state in RustIR *)

Inductive function_entry_mem_error (f: function) (vargs: list val) (m: mem) (e: env) : Prop :=
  | function_entry_mem_error_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters_mem_error ge e m1 f.(fn_params) vargs ->
      function_entry_mem_error f vargs m e.

Inductive step_mem_error : state -> Prop :=
| step_assign_error1: forall f e p k le m,
    eval_place_mem_error ge le m p ->
    step_mem_error (State f (Sassign p e) k le m)
| step_assign_error2: forall f e p k le m b ofs,
    eval_place ge le m p b ofs ->
    eval_expr_mem_error ge le m ge e ->
    step_mem_error (State f (Sassign p e) k le m)
| step_assign_error3: forall f e p k le m b ofs v v1 ty,
    eval_place ge le m p b ofs ->
    eval_expr ge le m ge e v ->
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    assign_loc_mem_error ge ty m b ofs v1 ->
    step_mem_error (State f (Sassign p e) k le m)
| step_assign_variant_error1: forall f e p k le m enum_id fid,
    (* error in evaluating lhs *)
    eval_place_mem_error ge le m p ->
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le m)
| step_assign_variant_error2: forall f e p k le m b ofs enum_id fid,
    (* error in storing the tag *)
    eval_place ge le m p b ofs ->
    ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable ->
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le m)
| step_assign_variant_error3: forall f e p k le m m' tag b ofs enum_id fid co orgs,
    typeof_place p = Tvariant orgs enum_id ->
    eval_place ge le m p b ofs ->
    ge.(genv_cenv) ! enum_id = Some co ->   
    field_tag fid (co_members co) = Some tag ->
    Mem.storev Mint32 m (Vptr b ofs) (Vint (Int.repr tag)) = Some m' ->    
    (* error in evaluating the rhs *)
    eval_expr_mem_error ge le m' ge e ->
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le m)
| step_assign_variant_error4: forall f e p k le m1 m2 b ofs enum_id fid v v1 ty co tag orgs,
    typeof_place p = Tvariant orgs enum_id ->
    ge.(genv_cenv) ! enum_id = Some co ->
    field_type fid (co_members co) = OK ty ->
    eval_place ge le m1 p b ofs ->
    sem_cast v (typeof e) ty = Some v1 ->
    field_tag fid (co_members co) = Some tag ->
    Mem.storev Mint32 m1 (Vptr b ofs) (Vint (Int.repr tag)) = Some m2 ->
    eval_expr ge le m2 ge e v ->
    (* error in evaluating the address of the downcast *)
    eval_place_mem_error ge le m2 (Pdowncast p fid ty) ->
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le m1)
| step_assign_variant_error5: forall f e p k le m1 m2 b ofs enum_id fid v v1 ty co tag orgs b1 ofs1,
    typeof_place p = Tvariant orgs enum_id ->
    ge.(genv_cenv) ! enum_id = Some co ->
    field_type fid (co_members co) = OK ty ->
    eval_place ge le m1 p b ofs ->
    sem_cast v (typeof e) ty = Some v1 ->
    field_tag fid (co_members co) = Some tag ->
    Mem.storev Mint32 m1 (Vptr b ofs) (Vint (Int.repr tag)) = Some m2 ->
    eval_expr ge le m2 ge e v ->
    eval_place_mem_error ge le m2 (Pdowncast p fid ty) ->
    eval_place ge le m2 (Pdowncast p fid ty) b1 ofs1 ->
    (* error in storing the rhs to downcast *)
    assign_loc_mem_error ge ty m2 b1 ofs1 v1 ->
    step_mem_error (State f (Sassign_variant p enum_id fid e) k le m1)                   
| step_box_error1: forall le e p k m1 m2 f b ty,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    (* error in storing the size *)
    ~ Mem.valid_access m2 Mptr b (- size_chunk Mptr) Writable ->
    step_mem_error (State f (Sbox p e) k le m1)
| step_box_error2: forall le e p k m1 m2 m3 f b ty,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    (* error in evaluating the rhs *)
    eval_expr_mem_error ge le m3 ge e ->
    step_mem_error (State f (Sbox p e) k le m1)
| step_box_error3: forall le e p k m1 m2 m3 f b ty v v1,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    (* error in storing the rhs *)
    assign_loc_mem_error ge ty m3 b Ptrofs.zero v1 ->
    step_mem_error (State f (Sbox p e) k le m1)
| step_box_error4: forall le e p k m1 m2 m3 m4 f b ty v v1,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    (* error in evaluating the address of lhs *)
    eval_place_mem_error ge le m4 p ->
    step_mem_error (State f (Sbox p e) k le m1)
| step_box_error5: forall le e p k m1 m2 m3 m4 f b ty v v1 pb pofs,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    eval_place ge le m4 p pb pofs ->
    (* error in assigning the allocated block to the lhs *)
    assign_loc_mem_error ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) ->
    step_mem_error (State f (Sbox p e) k le m1)
| step_drop_box_error1: forall le m k f p
    (PADDR: eval_place_mem_error ge le m p),
    step_mem_error (State f (Sdrop p) k le m)
| step_drop_box_error2: forall le m k f b ofs p ty
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc_mem_error (Tbox ty) m b ofs),
    step_mem_error (State f (Sdrop p) k le m)
| step_drop_box_error3: forall le m k f b ofs p ty b' ofs'
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (FREE: extcall_free_sem_mem_error [Vptr b' ofs'] m),
    step_mem_error (State f (Sdrop p) k le m)
| step_drop_struct_error: forall p orgs id m k f le
    (PTY: typeof_place p = Tstruct orgs id)
    (PADDR: eval_place_mem_error ge le m p),
    step_mem_error (State f (Sdrop p) k le m)
| step_drop_enum_error1: forall p orgs id m k f le
    (PTY: typeof_place p = Tvariant orgs id)
    (* error in evaluating the place *)
    (PADDR: eval_place_mem_error ge le m p),
    step_mem_error (State f (Sdrop p) k le m)
| step_drop_enum_error2: forall m k p orgs id b ofs f le
    (PTY: typeof_place p = Tvariant orgs id)
    (PADDR: eval_place ge le m p b ofs)
    (* error in loading the tag *)
    (* load tag  *)
    (TAG: ~Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable),
    step_mem_error (State f (Sdrop p) k le m)
| step_dropstate_error: forall id v s membs k m,
    step_drop_mem_error (Dropstate id v s membs k m) ->
    step_mem_error (Dropstate id v s membs k m)
                   
| step_call_error: forall f a al k le m  tyargs vf fd cconv tyres p orgs org_rels,
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge le m ge a vf ->
    eval_exprlist_mem_error ge le m ge al tyargs ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    step_mem_error (State f (Scall p a al) k le m)
| step_internal_function_error: forall vf f vargs k m e
    (FIND: Genv.find_funct ge vf = Some (Internal f)),
    function_entry_mem_error f vargs m e ->
    step_mem_error (Callstate vf vargs k m)
(* | step_return_0_error: forall f k le m, *)
(*     Mem.free_list m (blocks_of_env ge le) = None -> *)
(*     step_mem_error (State f (Sreturn None) k le m) *)
| step_return_1_error1: forall f p k le m,
    eval_expr_mem_error ge le m ge (Epure (Eplace p (typeof_place p))) ->
    step_mem_error (State f (Sreturn p) k le m)
| step_return_2_error2: forall f p k le m v,
    eval_expr ge le m ge (Epure (Eplace p (typeof_place p))) v ->
    Mem.free_list m (blocks_of_env ge le) = None ->
    step_mem_error (State f (Sreturn p) k le m)
| step_skip_call_error: forall f k le m,
    is_call_cont k ->
    Mem.free_list m (blocks_of_env ge le) = None ->
    step_mem_error (State f Sskip k le m)
| step_returnstate_error1: forall p v m f k e,
    eval_place_mem_error ge e m p ->
    step_mem_error (Returnstate v (Kcall (Some p) f e k) m)
| step_returnstate_error2: forall p v m f k e b ofs ty,
    ty = typeof_place p ->
    eval_place ge e m p b ofs ->
    assign_loc_mem_error ge ty m b ofs v ->
    step_mem_error (Returnstate v (Kcall (Some p) f e k) m)
| step_ifthenelse_error:  forall f a s1 s2 k e m,
    eval_expr_mem_error ge e m ge a ->
    step_mem_error (State f (Sifthenelse a s1 s2) k e m)
.
         

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.

Require Import InjectFootprint.

(** Where to put? A useful lemma for extcall_free_sem *)

Lemma extcall_free_injp: forall se tse v tv m m' tm t j Hm,
    extcall_free_sem se (v::nil) m t Vundef m' ->
    Val.inject j v tv ->
    exists tm' Hm',
      extcall_free_sem tse (tv::nil) tm t Vundef tm'
      /\ injp_acc (injpw j m tm Hm) (injpw j m' tm' Hm').
Proof.
  intros until Hm.
  intros FREE VINJ.
  inv FREE. inv VINJ.
  exploit Mem.load_inject; eauto.
  intros (v2 & LOAD & VINJ).
  exploit Mem.free_parallel_inject; eauto.
  intros (m2' & TFREE & MINJ).
  assert (P: Mem.range_perm m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
  (* refer the proof of extcall_free in Event: use address_inject *)  
  exploit Mem.address_inject. eapply Hm.
  apply Mem.perm_implies with Freeable; auto with mem.
  apply P. instantiate (1 := lo).
  generalize (size_chunk_pos Mptr); lia. eauto.
  intros EQ.
  assert (injp_acc (injpw j m tm Hm) (injpw j m' m2' MINJ)).
  replace (Ptrofs.unsigned lo + Ptrofs.unsigned sz) with ((Ptrofs.unsigned lo - size_chunk Mptr) + (size_chunk Mptr + Ptrofs.unsigned sz)) in * by lia.
  exploit injp_acc_free; eauto. 
  assert (v2 = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv VINJ; auto. }
  subst.
  exists m2', MINJ. split; auto.  
  econstructor. erewrite <- LOAD. f_equal. lia.
  auto. 
  rewrite ! EQ. rewrite <- TFREE. f_equal; lia.
  auto.
  (* case 2 *)
  exists tm, Hm. split.
  replace tv with Vnullptr.
  econstructor.
  unfold Vnullptr in *.
  destruct (Archi.ptr64); inv VINJ; auto.
  reflexivity.
Qed.  
  
