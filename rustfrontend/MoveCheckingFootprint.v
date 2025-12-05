Require Import Coqlib .
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepLinking SmallstepLinkingSafe.
Require Import LanguageInterface CKLR Invariant.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustOp RustIR RustIRcfg Rusttyping.
Require Import Errors.
Require Import InitDomain InitAnalysis.
Require Import RustIRown MoveChecking BorrowCheck.
Require Import Wfsimpl.

Import ListNotations.

(** The abstract domain used in the definition of invariant for
proving the safety of move checking. In particular, we use footprint
as the abstract value and fp_frame as the abstract memory. They are
some kinds of separation algebra, but we do not generalize it for
now. *)

(** Definition of footprint *)

(* A tree structured footprint (maybe similar to some separation logic
algebra) *)
Inductive footprint : Type :=
| fp_emp                      (* empty footprint *)
| fp_scalar (ty: type)        (* type must be scalar type  *)
| fp_box (b: block) (sz: Z) (fp: footprint) (* A heap block storing values that occupy footprint fp *)
(* (field ident, field type, field offset,field footprint) *)
| fp_struct (id: ident) (fpl: list (ident * Z * footprint))
(* orgs are not used for now but it is used to relate to the type *)
| fp_enum (id: ident) (orgs: list origin) (tag: Z) (fid: ident) (ofs: Z) (fp: footprint)
.
(* with field_footprint : Type := *)
(* | fp_field (fid: ident) (fty: type) (ofs: Z) (fp: footprint). *)

Section FP_IND.

Variable (P: footprint -> Prop)
  (HPemp: P fp_emp)
  (HPscalar: forall ty, P (fp_scalar ty))
  (HPbox: forall (b : block) sz (fp : footprint), P fp -> P (fp_box b sz fp))
  (HPstruct: forall id fpl, (forall fid ofs fp, In (fid, ofs, fp) fpl -> P fp) -> P (fp_struct id fpl))
  (HPenum: forall id orgs (tag : Z) fid ofs (fp : footprint), P fp -> P (fp_enum id orgs tag fid ofs fp)).

Fixpoint strong_footprint_ind t: P t.
Proof.
  destruct t.
  - apply HPemp.
  - apply HPscalar.
  - eapply HPbox. specialize (strong_footprint_ind t); now subst.
  - eapply HPstruct. induction fpl.
    + intros. inv H.
    + intros. destruct a as ((fid1 & ofs1) & fp1).  simpl in H. destruct H.
      * specialize (strong_footprint_ind fp1). inv H. apply strong_footprint_ind.
        (* now subst. *)
      * apply (IHfpl fid ofs fp H). 
  - apply HPenum. apply strong_footprint_ind.
Qed.
    
End FP_IND.

(* Footprint used in interface (for now, it is just defined by
support) *)
Definition flat_footprint : Type := list block.

(* Function used to flatten a footprint  *)
Fixpoint footprint_flat (fp: footprint) : flat_footprint :=
  match fp with
  | fp_emp => nil
  | fp_scalar _ => nil
  | fp_box b _ fp' =>
      b :: footprint_flat fp'
  | fp_struct _ fpl =>
      flat_map (fun '(_, _, fp) => footprint_flat fp) fpl
  | fp_enum _ _ _ _ _ fp =>
      footprint_flat fp
  end.

Definition footprint_disjoint (fp1 fp2: footprint) :=
  list_disjoint (footprint_flat fp1) (footprint_flat fp2).

Inductive footprint_disjoint_list : list footprint -> Prop :=
| fp_disjoint_nil: footprint_disjoint_list nil
| fp_disjoint_cons: forall fp fpl,
      list_disjoint (footprint_flat fp) (flat_map footprint_flat fpl) ->
      footprint_disjoint_list fpl ->
      footprint_disjoint_list (fp::fpl)
.

(* Definition of footprint map *)

Definition fp_map := PTree.t footprint.

(* A footprint in a function frame *)

Definition flat_fp_map (fpm: fp_map) : flat_footprint :=
  flat_map (fun elt => footprint_flat (snd elt)) (PTree.elements fpm).

(* Definiton of footprint for stack frames *)

(** Footprint map which records the footprint starting from stack
blocks (denoted by variable names). It represents the ownership chain
from a stack block. *)

(* The footprint in a module (similar to continuation) *)

Inductive fp_frame : Type :=
| fpf_emp
(* we need to record the footprint of the stack *)
| fpf_func (e: env) (fpm: fp_map) (fpf: fp_frame)
(* use this to record the structure of footprint in dropplace state, rfp is the footprint of the place being dropped *)
| fpf_dropplace (e: env) (fpm: fp_map) (rfp: footprint) (fpf: fp_frame)
(* record the footprint in a drop glue: fp is the footprint being
dropped and fpl is the footprint of the members to be dropped *)
| fpf_drop (fp: footprint) (fpl: list footprint) (fpf: fp_frame)
.

Definition footprint_of_env (e: env) : flat_footprint :=
  map (fun elt => fst (snd elt)) (PTree.elements e).


Fixpoint flat_fp_frame (fpf: fp_frame) : flat_footprint :=
  match fpf with
  | fpf_emp => nil
  | fpf_func e fpm fpf =>
      footprint_of_env e ++ flat_fp_map fpm ++ flat_fp_frame fpf
  | fpf_dropplace e fpm rfp fpf =>
      footprint_of_env e ++ flat_fp_map fpm ++ footprint_flat rfp ++ flat_fp_frame fpf
  | fpf_drop fp fpl fpf =>
      footprint_flat fp ++ flat_map footprint_flat fpl ++ flat_fp_frame fpf
  end.

Lemma in_footprint_of_env: forall b ty id le,
    le ! id = Some (b, ty) ->
    In b (footprint_of_env le).
Proof.
  intros. unfold footprint_of_env.
  eapply in_map_iff.
  exists (id, (b, ty)). split; auto.
  eapply PTree.elements_correct. eauto.
Qed.

Lemma in_footprint_of_env_inv: forall b le,    
    In b (footprint_of_env le) ->
    exists id ty, le ! id = Some (b, ty).
Proof.
  intros. unfold footprint_of_env in H.
  eapply in_map_iff in H.
  destruct H as ((id & (b1 & ty)) & A1 & A2).
  simpl in *. subst.
  exists id , ty. eapply PTree.elements_complete. eauto.
Qed.

Lemma in_footprint_flat_fp_map: forall b fp fpm id,
    fpm ! id = Some fp ->
    In b (footprint_flat fp) ->
    In b (flat_fp_map fpm).
Proof.
  intros. unfold flat_fp_map.
  eapply in_flat_map. exists (id, fp). split; auto.
  eapply PTree.elements_correct. auto.
Qed.


(* Key lemma to simplify the proof of set_disjoint_footprint_norepet *)
Lemma PTree_remove_elements_eq {A: Type}: forall id (v: A) m,
    PTree.elements (PTree.remove id m) = PTree.elements (PTree.remove id (PTree.set id v m)).
Proof.
  intros.
  eapply PTree.elements_extensional.
  intros. rewrite !PTree.grspec.
  destruct PTree.elt_eq; subst; auto.
  rewrite PTree.gso; eauto.
Qed.

Lemma PTree_remove_elements_eq2 {A: Type}: forall id (v: A) m,
    m ! id = None ->
    PTree.elements m = PTree.elements (PTree.remove id (PTree.set id v m)).
Proof.
  intros.
  eapply PTree.elements_extensional.
  intros. rewrite !PTree.grspec.
  destruct PTree.elt_eq; subst; auto.
  rewrite PTree.gso; eauto.
Qed.

Lemma cons_app {A: Type}: forall a (l: list A),
    a :: l = (a::nil) ++ l.
Proof. reflexivity. Qed.
  

Lemma set_env_footprint_norepet: forall e1 id ty b,
    list_norepet (footprint_of_env e1) ->
    ~ In b (footprint_of_env e1) ->
    list_norepet (footprint_of_env (PTree.set id (b, ty) e1)).
Proof.
  intros until b. intros NOREP NIN.
  unfold footprint_of_env in *.
  exploit PTree.elements_remove.
  instantiate (3 := (PTree.set id (b, ty) e1)).
  eapply PTree.gss. intros (l3 & l4 & A3 & A4).
  rewrite A3.
  rewrite map_app. simpl.
  rewrite cons_app.     
  eapply list_norepet_append_commut2. rewrite app_assoc. rewrite <- map_app.
  destruct (e1 ! id) eqn: E1.
  exploit PTree.elements_remove.
  instantiate (3 := e1).
  eauto. intros (l1 & l2 & A1 & A2).
  erewrite <- PTree_remove_elements_eq in A4. rewrite A4 in A2. 
  rewrite A2.
  rewrite A1 in *. rewrite map_app in NOREP. simpl in NOREP.
  rewrite cons_app in NOREP.
  eapply list_norepet_append_commut2 in NOREP. rewrite app_assoc in NOREP.
  rewrite <- map_app in NOREP.
  eapply list_norepet_app in NOREP as (N1 & N2 & N3). eapply list_norepet_app.
  repeat apply conj; auto.
  eapply list_norepet_cons. simpl. auto. eapply list_norepet_nil.
  red. intros. intro. subst. eapply NIN.
  inv H0; try contradiction.
  eapply in_map_iff in H. destruct H as ((id1 & (b1 & ty1)) & IN1 & IN2). simpl in *.
  subst.
  eapply in_map_iff. exists (id1, (y, ty1)). split; auto.
  rewrite in_app in IN2. rewrite in_app. destruct IN2; auto.
  right. eapply in_cons; auto.
  erewrite <- PTree_remove_elements_eq2 in A4; auto. rewrite A4 in *. 
  eapply list_norepet_app.
  repeat apply conj; auto.
  eapply list_norepet_cons. simpl. auto. eapply list_norepet_nil.
  red. intros. intro. subst. eapply NIN.
  inv H0; try contradiction.
Qed.   


(* Try to define new sem_wt *)

Definition find_fields (fid: ident) (fpl: list (ident * Z * footprint)) : option (ident * Z * footprint) :=
  find (fun '(fid', _, _) => if ident_eq fid fid' then true else false) fpl. 

(* Definition set_field (fid: ident) (vfp: footprint) (fpl: list (ident * Z * footprint)) : list (ident * Z * footprint) := *)
(*   (map *)
(*      (fun '(fid2, fofs2, ffp2) => *)
(*         if ident_eq fid fid2 then (fid2, fofs2, vfp) else (fid2, fofs2, ffp2)) fpl). *)

(* only set the first occurence of fid *)
Fixpoint set_field (fid: ident) (vfp: footprint) (fpl: list (ident * Z * footprint)) : list (ident * Z * footprint) :=
  match fpl with
  | nil => nil
  | (fid', fofs, ffp) :: fpl' =>
      if ident_eq fid fid' then
        (fid, fofs, vfp) :: fpl'
      else
        (fid', fofs, ffp) :: (set_field fid vfp fpl')
  end.


Lemma find_fields_some: forall fid fid1 fpl fofs ffp,
    find_fields fid fpl = Some (fid1, fofs, ffp) ->
    fid = fid1 /\ In (fid, fofs, ffp) fpl.
Proof.
  intros. unfold find_fields in H.
  exploit find_some; eauto. intros (A & B).
  destruct ident_eq in B; try congruence.
  subst. auto.
Qed.

Lemma find_fields_different_field: forall fpl fid id fofs ffp vfp,
    id <> fid ->
    find_fields fid (set_field id vfp fpl) = Some (fid, fofs, ffp) ->
    find_fields fid fpl = Some (fid, fofs, ffp).
Proof.
  induction fpl; intros; simpl in *; try congruence.
  destruct a. destruct p. destruct ident_eq in H0.
  - subst. destruct ident_eq.
    + subst. congruence.
    + simpl in H0. destruct ident_eq in H0; try congruence.
  - destruct ident_eq.
    + subst. simpl in H0. destruct ident_eq in H0; try congruence.
    + simpl in H0. destruct ident_eq in H0; try congruence.
      eauto.
Qed.

Ltac simpl_find_fields :=
  match goal with
  | [H :find_fields _ (_ :: _) = Some _ |- _ ] =>
      simpl; simpl in H;
      destruct ident_eq; try congruence
  | [ |- find_fields _ (_ :: _) = Some _ ] =>
      simpl;
      destruct ident_eq; try congruence
  end.

Lemma find_fields_same_offset: forall fpl fid id fofs ffp vfp,
    find_fields fid (set_field id vfp fpl) = Some (fid, fofs, ffp) ->
    exists vfp1, find_fields fid fpl = Some (fid, fofs, vfp1).
Proof.
  induction fpl; intros; simpl in *; try congruence.
  destruct a. destruct p. destruct ident_eq in H.
  - subst. simpl_find_fields.
    + inv H. eauto.
    + eauto.
  - simpl_find_fields.
    + inv H. eauto.
    + eauto.
Qed.

Lemma find_fields_same_footprint: forall fpl fid fofs ffp vfp,
    find_fields fid (set_field fid vfp fpl) = Some (fid, fofs, ffp) ->
    vfp = ffp.
Proof.
  induction fpl; intros; simpl in *; try congruence.
  destruct a. destruct p. destruct ident_eq in H.
  - subst. simpl_find_fields.
  - simpl_find_fields. eauto.
Qed.

Lemma find_fields_set_spec: forall fpl fid1 fid2 fofs ffp vfp,
    find_fields fid1 fpl = Some (fid1, fofs, ffp) ->
    find_fields fid1 (set_field fid2 vfp fpl) = Some (fid1, fofs, if peq fid1 fid2 then vfp else ffp).
Proof.
  induction fpl; intros; simpl in *; try congruence.
  destruct a. destruct p.
  destruct ident_eq in H.
  - subst. inv H. destruct ident_eq; subst.
    + destruct ident_eq; try congruence.
      simpl. destruct ident_eq; try congruence.
      auto.
    + simpl_find_fields.
      destruct peq; try congruence. auto.
  - destruct ident_eq; subst.
    + simpl_find_fields.
    + simpl_find_fields. eauto.
Qed.

Definition name_footprints (fpl: list (ident * Z * footprint)) : list ident :=
  map (fun '(fid, _, _) => fid) fpl.

Lemma find_fields_split: forall fpl id fofs ffp,
    find_fields id fpl = Some (id, fofs, ffp) ->
    exists l1 l2,
      fpl = l1 ++ (id, fofs, ffp) :: l2
      /\ ~ In id (name_footprints l1).
Proof.
  induction fpl; simpl; intros.
  - inv H.
  - destruct a. destruct p.
    destruct ident_eq.
    + inv H. exists nil, fpl.
      split. simpl. auto.
      intro. inv H.
    + exploit IHfpl; eauto. intros (l1 & l2 & A1 & A2).
      subst.
      exists ((i,z,f)::l1), l2. split; auto.
      intro. inv H0; congruence. 
Qed.
      
Lemma set_fields_split: forall l1 l2 id fofs ffp ffp1,
    ~ In id (name_footprints l1) ->
    set_field id ffp1 (l1 ++ (id, fofs, ffp) :: l2 ) = (l1 ++ (id, fofs, ffp1) :: l2).
Proof.
  induction l1; simpl; intros.
  - destruct ident_eq; try congruence.
  - destruct a. destruct p. eapply Decidable.not_or in H.
    destruct H. destruct ident_eq; try congruence.
    f_equal. eauto.
Qed.


(** Definition of path disjointness in the footprint *)

Inductive paths_disjoint : list path -> list path -> Prop :=
| phs_disjoint1: forall p1 p2 l1 l2,
    (* Is it enough to use neq? *)
    p1 <> p2 ->
    paths_disjoint (p1::l1) (p2::l2)
| phs_disjoint2: forall p l1 l2,
    paths_disjoint l1 l2 ->
    paths_disjoint (p::l1) (p::l2).

Lemma paths_disjoint_sym: forall phl1 phl2,
    paths_disjoint phl1 phl2 ->
    paths_disjoint phl2 phl1.
Proof.
  induction 1.
  econstructor. eauto.
  eapply phs_disjoint2; auto.
Qed.

Lemma local_of_paths_of_place: forall p,
    local_of_place p = fst (path_of_place p).
Proof.
  induction p; simpl; auto; destruct (path_of_place p); auto.
Qed.


Lemma paths_not_contain_disjoint: forall l1 l2,
    paths_contain l1 l2 = false ->
    paths_contain l2 l1 = false ->
    paths_disjoint l1 l2.
Proof.
  induction l1; intros; simpl in *.
  - congruence.
  - destruct l2; simpl in *; try congruence.
    destruct path_eq; subst; destruct path_eq; try congruence.
    eapply phs_disjoint2. auto.
    eapply phs_disjoint1; auto.
Qed.

Lemma is_not_prefix_disjoint: forall p1 p2,
    is_prefix p1 p2 = false ->
    is_prefix p2 p1 = false ->
    fst (path_of_place p1) <> fst (path_of_place p2) \/
      paths_disjoint (snd (path_of_place p1)) (snd (path_of_place p2)).
Proof.
  intros. unfold is_prefix in *.
  destruct (path_of_place p1) eqn: POP1.
  destruct (path_of_place p2) eqn: POP2.  
  simpl.
  destruct ident_eq in H; destruct ident_eq in H0; subst;  simpl in *; try congruence; auto.
  right. eapply paths_not_contain_disjoint; auto.
Qed.  

Lemma paths_contain_app_inv: forall l1 l2,
    paths_contain l1 l2 = true ->
    exists l3, l2 = l1 ++ l3.
Proof.
  induction l1; intros; simpl in *; eauto.
  destruct l2; try congruence; eauto.
  destruct path_eq; subst; try congruence; eauto.
  exploit IHl1; eauto. intros (l3 & A1). subst. eauto.
Qed.

Lemma is_prefix_paths_app: forall p1 p2,
    is_prefix p1 p2 = true ->
    fst (path_of_place p1) = fst (path_of_place p2)
    /\ exists phl, snd (path_of_place p2) = snd (path_of_place p1) ++ phl.
Proof.
  intros. destr_prefix.
  split. auto.
  eapply paths_contain_app_inv. eauto.
Qed.

Lemma paths_disjoint_app: forall l1 l2 l3,
    paths_disjoint (l1 ++ l2) l3 ->
    (exists l2', l3 = l1 ++ l2' /\ paths_disjoint l2 l2')
    \/ paths_disjoint l1 l3.
Proof.
  induction l1; intros.
  - left. exists l3. eauto.
  - inv H.
    + right. eapply phs_disjoint1. eauto.
    + eapply IHl1 in H3.
      destruct H3.
      * destruct H as (l2' & A1 & A2). subst.
        left. eexists. split; eauto.
        reflexivity.
      * right. eapply phs_disjoint2; eauto.
Qed.

(** * Functions and properties for updating the footprint *)

(** Prove some properties w.r.t list_nth_z  *)
Fixpoint list_set_nth_z {A: Type} (l: list A) (n: Z) (v: A)  {struct l}: list A :=
  match l with
  | nil => nil
  | hd :: tl => if zeq n 0 then (v :: tl) else hd :: (list_set_nth_z tl (Z.pred n) v)
  end.

(* set footprint [v] in the path [ph] of footprint [fp] *)
Fixpoint set_footprint (phl: list path) (v: footprint) (fp: footprint) : option footprint :=
  match phl with
  | nil => Some v
  | ph :: l =>
        match ph, fp with
        | ph_deref, fp_box b sz fp1 =>
            match set_footprint l v fp1 with
            | Some fp2 =>
                Some (fp_box b sz fp2)
            | None => None
            end
        | ph_field fid, fp_struct id fpl =>
            match find_fields fid fpl with
            | Some (fid1, fofs, ffp) =>                
                match set_footprint l v ffp with
                | Some ffp1 =>
                    Some (fp_struct id (set_field fid ffp1 fpl)) 
                | None => None
                end
            | None => None
            end
        | ph_downcast pty fid (* fty *), fp_enum id orgs tagz fid1 fofs1 fp1 =>
            match pty with
            | Tvariant orgs1 id1 =>
                if ident_eq id1 id then
                  if list_eq_dec ident_eq orgs1 orgs then
                    if ident_eq fid fid1 then
                      match set_footprint l v fp1 with
                      | Some fp2 =>
                          Some (fp_enum id orgs tagz fid1 fofs1 fp2)
                      | None => None
                      end
                    else None
                  else None
                else None
            | _ => None
            end
        | _, _ => None
        end
  end.

Fixpoint clear_footprint_rec (fp: footprint) : footprint :=
  match fp with
  | fp_scalar _
  | fp_box _ _ _
  | fp_enum _ _ _ _ _ _
  | fp_emp => fp_emp
  | fp_struct id fpl =>
      fp_struct id (map (fun '(fid, fofs, ffp) => (fid, fofs, clear_footprint_rec ffp)) fpl)
  end.

Fixpoint get_loc_footprint (phl: list path) (fp: footprint) (b: block) (ofs: Z) : option (block * Z * footprint) :=
  match phl with
  | nil => Some (b, ofs, fp)
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b _ fp1 =>
          get_loc_footprint l fp1 b 0
      | ph_field fid, fp_struct _ fpl =>
          match find_fields fid fpl with
          | Some (_, fofs, fp1) =>
              get_loc_footprint l fp1 b (ofs + fofs)
          | None => None
          end
      | ph_downcast pty fid1 (* fty1 *), fp_enum id orgs _ fid2 fofs fp1 =>
          match pty with
          | Tvariant orgs1 id1 =>
              if ident_eq id1 id then
                if list_eq_dec ident_eq orgs1 orgs then
                if ident_eq fid1 fid2  then
                  get_loc_footprint l fp1 b (ofs + fofs)
                else
                  None
                else None
              else None
          | _ => None
          end
      | _, _  => None
      end
  end.

(* non-loc version: use it to get some internal footprint *)
Fixpoint get_footprint (phl: list path) (fp: footprint) : option footprint :=
  match phl with
  | nil => Some fp
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b _ fp1 =>
          get_footprint l fp1
      | ph_field fid, fp_struct _ fpl =>
          match find_fields fid fpl with
          | Some (_, fofs, fp1) =>
              get_footprint l fp1
          | None => None
          end
      | ph_downcast pty fid1 (* fty1 *), fp_enum id orgs _ fid2 fofs fp1 =>
          match pty with
          | Tvariant orgs1 id1 =>
              if ident_eq id1 id then
                if list_eq_dec ident_eq orgs1 orgs then
                  if ident_eq fid1 fid2 then
                    get_footprint l fp1
                  else
                    None
                else None
              else None
          | _ => None
          end
      | _, _  => None
      end
  end.


(* Definition clear_footprint (phl: list path) (fp: footprint) : option footprint := *)
(*   match get_footprint phl fp with *)
(*   | Some fp1 => *)
(*       set_footprint phl (clear_footprint_rec fp1) fp *)
(*   | None => None *)
(*   end. *)


Definition set_footprint_map (ps: paths) (v: footprint) (fpm: fp_map) : option fp_map :=
  let (id, phl) := ps in
  match fpm!id with
  | Some fp1 =>
      match set_footprint phl v fp1 with
      | Some fp2 =>
          Some (PTree.set id fp2 fpm)
      | None =>
          None
      end
  | None => None
  end.


Definition get_loc_footprint_map (e: env) (ps: paths) (fpm: fp_map) : option (block * Z * footprint) :=
  let (id, phl) := ps in
  match e!id, fpm!id with
  | Some (b, ty), Some fp =>
      get_loc_footprint phl fp b 0
  | _, _ => None
  end.


(* Definition get_footprint_map (ps: paths) (fpm: fp_map) : option footprint := *)
(*   let (id, phl) := ps in *)
(*   match fpm!id with *)
(*   | Some fp => *)
(*       get_footprint phl fp *)
(*   | None => None *)
(*   end. *)

Definition clear_footprint_map e (ps: paths) (fpm: fp_map) : option fp_map :=
  match get_loc_footprint_map e ps fpm with
  | Some (_, _, fp1) =>
      set_footprint_map ps (clear_footprint_rec fp1) fpm
  | None => None
  end.

(* Useful tactic to destruct get_loc_footprint *)
Ltac destr_fp_enum fp ty :=
  destruct fp; try congruence;
  destruct ty; try congruence;
  destruct ident_eq; try congruence;
  destruct list_eq_dec; try congruence;
  destruct ident_eq; try congruence; subst.

Ltac destr_fp_enum_simpl fp :=
  destruct fp; try congruence;
  destruct ident_eq; try congruence;
  destruct list_eq_dec; try congruence;
  destruct ident_eq; try congruence; subst.

Ltac destr_fp_field fp H :=
  let A1 := fresh "A" in
  let A2 := fresh "A" in
  let p := fresh "p" in
  let FIND := fresh "FIND" in
  destruct fp; try congruence;
  destruct find_fields as [p|] eqn: FIND; try congruence;
  repeat destruct p; simpl in H;
exploit find_fields_some; eauto; intros (A1 & A2); subst.


Lemma get_loc_footprint_app: forall phl1 phl2 fp fp1 b ofs b1 ofs1 b2 ofs2 fp2,
    get_loc_footprint phl1 fp b ofs = Some (b1, ofs1, fp1) ->
    get_loc_footprint phl2 fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    get_loc_footprint (phl1 ++ phl2) fp b ofs = Some (b2, ofs2, fp2).
Proof.
  induction phl1; simpl; intros.
  - inv H. auto.
  - destruct a.
    + destruct fp; try congruence.
      eauto.
    + destr_fp_field fp H.
    + destr_fp_enum fp ty.
      eauto.
Qed.
         
Lemma get_loc_footprint_map_app: forall phl2 phl1 id e fpm b ofs fp b1 ofs1 fp1,
    get_loc_footprint_map e (id, phl1) fpm = Some (b, ofs, fp) ->
    get_loc_footprint phl2 fp b ofs = Some (b1, ofs1, fp1) ->
    get_loc_footprint_map e (id, phl1 ++ phl2) fpm = Some (b1, ofs1, fp1).
Proof.
  induction phl2; intros.
  - simpl in H0. inv H0. rewrite app_nil_r. auto.
  - unfold get_loc_footprint_map in H.
    destruct (e ! id) eqn: ID; try congruence. destruct p.
    destruct (fpm ! id) eqn: FPM; try congruence.     
    replace (a :: phl2) with ((a::nil) ++ phl2) by auto.
    rewrite app_assoc.
    simpl in H0. destruct a.
    + destruct fp; try congruence.          
      eapply IHphl2. 
      unfold get_loc_footprint_map. rewrite ID. rewrite FPM.
      eapply get_loc_footprint_app. eauto.
      simpl. eauto. auto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      eapply IHphl2. 
      unfold get_loc_footprint_map. rewrite ID. rewrite FPM.
      eapply get_loc_footprint_app. eauto.
      simpl. rewrite FIND. eauto. auto.
    + destruct fp; try congruence.
      destruct ty; try congruence. destruct ident_eq in H0; try congruence. subst.
      destruct list_eq_dec in H0; try congruence.
      destruct ident_eq in H0; simpl in H0; try congruence. subst.            
      (* destruct type_eq in H0; simpl in H0; try congruence. subst. *)
      eapply IHphl2. 
      unfold get_loc_footprint_map. rewrite ID. rewrite FPM.
      eapply get_loc_footprint_app. eauto.
      simpl. destruct ident_eq; simpl; try congruence.
      destruct ident_eq; simpl; try congruence.
      destruct list_eq_dec; try congruence.
      (* destruct type_eq; simpl; try congruence. *)
      eauto. auto.
Qed.


Lemma get_loc_footprint_app_inv: forall phl1 phl2 b1 b2 ofs1 ofs2 fp1 fp2,
    get_loc_footprint (phl1 ++ phl2) fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    exists b3 ofs3 fp3,
      get_loc_footprint phl1 fp1 b1 ofs1 = Some (b3, ofs3, fp3)
      /\ get_loc_footprint phl2 fp3 b3 ofs3 = Some (b2, ofs2, fp2).
Proof.
  induction phl1; intros; simpl in *.
  - eauto.
  - destruct a.
    + destruct fp1; try congruence.
      eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      eauto.
    + destr_fp_enum fp1 ty.
      eauto.
Qed.

      
Lemma get_loc_footprint_map_app_inv: forall phl2 phl1 id e fpm b1 ofs1 fp1,
    get_loc_footprint_map e (id, phl1 ++ phl2) fpm = Some (b1, ofs1, fp1) ->
    exists b ofs fp,
      get_loc_footprint_map e (id, phl1) fpm = Some (b, ofs, fp)
      /\ get_loc_footprint phl2 fp b ofs = Some (b1, ofs1, fp1).
Proof.
  intros. simpl in *.
  destruct (e!id); try congruence.
  destruct p.
  destruct (fpm!id); try congruence.
  eapply get_loc_footprint_app_inv; eauto.
Qed.


Lemma get_set_footprint_exists: forall phl fp1 fp b ofs b1 ofs1 vfp,
    get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
    exists fp2, set_footprint phl vfp fp = Some fp2
           /\ get_loc_footprint phl fp2 b ofs = Some (b1, ofs1, vfp).
Proof.
  induction phl; simpl; intros.
  - inv H. eauto.
  - destruct a.
    + destruct fp; try congruence.
      exploit IHphl; eauto.
      instantiate (1 := vfp). intros (fp2 & A1 & A2).
      rewrite A1. eexists. split; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit IHphl; eauto.
      instantiate (1 := vfp). intros (fp2 & A1 & A2).
      rewrite A1.
      eexists; split; eauto.
      exploit find_fields_some; eauto. intros (B1 & B2). subst.
      simpl. erewrite find_fields_set_spec; eauto.
      destruct peq; try congruence.
    + destr_fp_enum fp ty.
      exploit IHphl; eauto.
      instantiate (1 := vfp). intros (fp2 & A1 & A2).
      rewrite A1.
      eexists; split; eauto.
      simpl. destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
Qed.
     
Lemma get_set_footprint_map_exists: forall phl id fp fp1 fpm1 b ofs le,
    get_loc_footprint_map le (id, phl) fpm1 = Some (b, ofs, fp1) ->
    exists fpm2, set_footprint_map (id, phl) fp fpm1 = Some fpm2
            /\ get_loc_footprint_map le (id, phl) fpm2 = Some (b, ofs, fp).
Proof.
  intros. simpl in *.
  destruct (le ! id) eqn: A; try congruence. destruct p.
  destruct (fpm1 ! id) eqn: B; try congruence.
  exploit get_set_footprint_exists; eauto. instantiate (1 := fp).
  intros (fp2 & A1 & A2). rewrite A1.
  eexists; split; eauto.
  rewrite PTree.gss. auto.
Qed.

Lemma get_set_footprint_app_inv: forall phl1 phl2 fp1 fp2 fp fp' b1 ofs1 b ofs,
    get_loc_footprint phl1 fp b ofs = Some (b1, ofs1, fp1) ->
    set_footprint (phl1++phl2) fp2 fp = Some fp' ->
    exists fp3,
      get_loc_footprint phl1 fp' b ofs = Some (b1, ofs1, fp3)
      /\ set_footprint phl2 fp2 fp1 = Some fp3.
Proof.
  induction phl1; simpl; intros.
  - inv H. eauto.
  - destruct a.
    + destruct fp; try congruence.
      destruct (set_footprint (phl1 ++ phl2) fp2 fp) eqn: A; try congruence.
      inv H0.
      exploit IHphl1; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      destruct (set_footprint (phl1 ++ phl2) fp2 f) eqn: A; try congruence.
      inv H0.
      exploit find_fields_some; eauto. intros (B1 & B2). subst.
      erewrite find_fields_set_spec; eauto.
      destruct peq; try congruence.
      eauto.
    + destr_fp_enum fp ty.
      destruct (set_footprint (phl1 ++ phl2) fp2 fp) eqn: A; try congruence.
      inv H0.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      eauto.
Qed.
      
Lemma get_set_footprint_map_app_inv: forall phl2 phl1 id fpm1 fpm2 fp1 fp2 b1 ofs1 le,
    get_loc_footprint_map le (id, phl1) fpm1 = Some (b1, ofs1, fp1) ->
    set_footprint_map (id, phl1++phl2) fp2 fpm1 = Some fpm2 ->
    exists fp3,
      get_loc_footprint_map le (id, phl1) fpm2 = Some (b1, ofs1, fp3)
      /\ set_footprint phl2 fp2 fp1 = Some fp3.
Proof.
  intros. simpl in *.
  destruct (le!id) eqn: A; try congruence. destruct p.
  destruct (fpm1!id) eqn: B; try congruence.
  destruct (set_footprint (phl1 ++ phl2) fp2 f) eqn: C; try congruence.
  inv H0. rewrite PTree.gss.
  eapply get_set_footprint_app_inv; eauto.
Qed.

Lemma set_footprint_app: forall l1 l2 fp1 fp1' fp2 fp fp',
         get_footprint l1 fp = Some fp1 ->
        set_footprint l2 fp2 fp1 = Some fp1' ->
        set_footprint l1 fp1' fp = Some fp' ->
        set_footprint (l1++l2) fp2 fp = Some fp'.
Proof.
  induction l1; intros.
  - simpl in *. inv H. inv H1. auto.
  - simpl in *. destruct a.
    + destruct fp; try congruence.
      destruct (set_footprint l1 fp1' fp) eqn: A; try congruence.
      inv H1. erewrite IHl1; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      destruct (set_footprint l1 fp1' f) eqn: SET; try congruence.
      inv H1. erewrite IHl1; eauto.
    + destruct fp; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      destruct (set_footprint l1 fp1' fp) eqn: SET; try congruence.
      erewrite IHl1; eauto.
Qed.

(** IMPORTANT TODO *)
Lemma set_footprint_app_inv : forall l1 l2 fp fp' vfp1,
    set_footprint (l1++l2) vfp1 fp = Some fp' ->
    exists fp'' vfp2,
      get_footprint l1 fp = Some fp''                                       
      /\ set_footprint l2 vfp1 fp'' = Some vfp2
      /\ set_footprint l1 vfp2 fp = Some fp'.
Proof.
  induction l1; intros.
  - simpl in H. exists fp, fp'. simpl.
    repeat apply conj; auto.
  - simpl in H. destruct a.
    + destruct fp; try congruence.
      destruct (set_footprint (l1 ++ l2) vfp1 fp) eqn: A; try congruence.
      inv H. exploit IHl1; eauto.
      intros (fp'' & vfp'2 & B1 & B2 & B3).
      simpl.
      exists fp'', vfp'2. repeat apply conj; auto.
      rewrite B3. auto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      destruct (set_footprint (l1 ++ l2) vfp1 f) eqn: A; try congruence.
      inv H. exploit IHl1; eauto.
      intros (fp'' & vfp'2 & B1 & B2 & B3).
      simpl. rewrite FIND.
      exists fp'', vfp'2. repeat apply conj; auto.
      rewrite B3. auto.
    + destruct fp; try congruence.
      destruct ty; try congruence.
      simpl.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      destruct (set_footprint (l1 ++ l2) vfp1 fp) eqn: A; try congruence.
      inv H. exploit IHl1; eauto.
      intros (fp'' & vfp'2 & B1 & B2 & B3).
      simpl.      
      exists fp'', vfp'2. repeat apply conj; auto.
      rewrite B3. auto.
Qed.

      
(* non-loc version of get_footprint_app *)
Lemma get_footprint_app: forall l1 l2 fp1 fp2 fp3,
    get_footprint l1 fp1 = Some fp2 ->
    get_footprint l2 fp2 = Some fp3 ->
    get_footprint (l1 ++ l2) fp1 = Some fp3.
Proof.
  induction l1; intros; simpl in *.
  - inv H. auto.
  - destruct a.
    + destruct fp1; try congruence.
      eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. eauto.
    + destruct fp1; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      eauto.
Qed.

Lemma get_footprint_app_inv: forall phl1 phl2 fp1 fp2,
    get_footprint (phl1 ++ phl2) fp1 = Some fp2 ->
    exists fp3,
      get_footprint phl1 fp1 = Some fp3
      /\ get_footprint phl2 fp3 = Some fp2.
Proof.
  induction phl1; simpl; intros; eauto.
  destruct a.
  - destruct fp1; try congruence.
    eauto.
  - destruct fp1; try congruence.
    destruct (find_fields fid fpl) eqn: FIND; try congruence.
    repeat destruct p. eauto.
  - destr_fp_enum fp1 ty.
    eauto.
Qed.
    
Lemma get_loc_footprint_eq: forall l fp b ofs b1 ofs1 fp1,
    get_loc_footprint l fp b ofs = Some (b1, ofs1, fp1) ->
    get_footprint l fp = Some fp1.
Proof.
  induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in *. destruct a.
    + destruct fp; try congruence.
      eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. eauto.
    + destruct fp; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      eauto.
Qed.

Lemma get_set_disjoint_paths_aux: forall phl1 phl2 fp1 fp2 fp b ofs,
    paths_disjoint phl1 phl2 ->
    set_footprint phl1 fp fp1 = Some fp2 ->
    get_loc_footprint phl2 fp1 b ofs = get_loc_footprint phl2 fp2 b ofs.
Proof.
  induction phl1; intros.
  - inv H.
  - inv H.
    + simpl in *.
      destruct a.
      * destruct fp1; try congruence.
        destruct (set_footprint phl1 fp fp1) eqn: A; try congruence.
        inv H0.
        destruct p2; try congruence; auto.
      * destruct fp1; try congruence.
        destruct (find_fields fid fpl) eqn: FIND; try congruence.
        repeat destruct p. 
        destruct (set_footprint phl1 fp f) eqn: A; try congruence.
        inv H0.
        destruct p2; try congruence; auto.
        destruct (ident_eq fid fid0); try congruence.
        exploit find_fields_some; eauto. intros (B1 & B2). subst.
        destruct (find_fields fid0 fpl) eqn: FIND1.
        -- repeat destruct p.
           exploit find_fields_some; eauto. intros (B3 & B4). subst.           
           erewrite find_fields_set_spec; eauto.
           destruct peq; try congruence.
        -- destruct (find_fields fid0 (set_field i f0 fpl)) eqn: F1; try congruence.
           repeat destruct p.
           exploit find_fields_some; eauto. intros (B3 & B4). subst.
           exploit find_fields_different_field; eauto. congruence.
      * destr_fp_enum fp1 ty.
        destruct (set_footprint phl1 fp fp1) eqn: A; try congruence.
        inv H0.
        destruct p2; try congruence.
        destruct (type_eq (Tvariant orgs id) ty); try congruence.
        -- subst.
           destruct (ident_eq fid0 fid); try congruence.
           destruct ident_eq; try congruence.
           destruct list_eq_dec; try congruence.
           destruct ident_eq; try congruence.
        -- destruct ty; try congruence.
           destruct ident_eq; try congruence.
           destruct list_eq_dec; try congruence.
    + simpl in *. destruct a.
      * destruct fp1; try congruence.
        destruct (set_footprint phl1 fp fp1) eqn: A; try congruence.
        inv H0. eauto.
      * destruct fp1; try congruence.
        destruct (find_fields fid fpl) eqn: FIND; try congruence.
        repeat destruct p. 
        destruct (set_footprint phl1 fp f) eqn: A; try congruence.
        inv H0.
        exploit find_fields_some; eauto. intros (B1 & B2). subst.
        erewrite find_fields_set_spec; eauto.
        destruct peq; try congruence. eauto.
      * destr_fp_enum fp1 ty.
        destruct (set_footprint phl1 fp fp1) eqn: A; try congruence.
        inv H0.
        destruct ident_eq; try congruence.
        destruct list_eq_dec; try congruence.
        destruct ident_eq; try congruence. eauto.
Qed.           
        
Lemma get_set_disjoint_paths : forall phl1 phl2 id e fpm1 fpm2 fp,
    paths_disjoint phl1 phl2 ->
    set_footprint_map (id, phl1) fp fpm1 = Some fpm2 ->
    get_loc_footprint_map e (id, phl2) fpm1 = get_loc_footprint_map e (id, phl2) fpm2.
Proof.
  intros. simpl in *.
  destruct (e!id) eqn: A; auto. destruct p.
  destruct (fpm1 ! id) eqn: B; try congruence.
  destruct (set_footprint phl1 fp f) eqn: C; try congruence.
  inv H0. rewrite PTree.gss.
  eapply get_set_disjoint_paths_aux; eauto.
Qed.

Lemma get_set_different_local : forall phl1 phl2 id1 id2 e fpm1 fpm2 fp,
    id1 <> id2 ->
    set_footprint_map (id1, phl1) fp fpm1 = Some fpm2 ->
    get_loc_footprint_map e (id2, phl2) fpm1 = get_loc_footprint_map e (id2, phl2) fpm2.
Proof.
  intros. simpl in *.
  destruct (e! id2) eqn: A; auto. destruct p.
  destruct (fpm1 ! id1) eqn: B; try congruence.
  destruct (set_footprint phl1 fp f) eqn: C; try congruence. inv H0.
  rewrite PTree.gso; eauto.
Qed.

(* The footprints of two different subfields are disjoint *)
Lemma footprint_norepet_fields_disjoint: forall (fpl: list (ident * Z * footprint)) id1 id2 fofs1 fofs2 fp1 fp2,
    list_norepet (flat_map (fun '(_, _, fp) => footprint_flat fp) fpl) ->
    In (id1, fofs1, fp1) fpl ->
    In (id2, fofs2, fp2) fpl ->
    id1 <> id2 ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2).
Proof.
  induction fpl; simpl; intros; try contradiction.
  destruct a. destruct p. 
  eapply list_norepet_app in H. destruct H as (A1 & A2 & A3).
  destruct H0; destruct H1.
  - inv H. inv H0. congruence.
  - inv H. red. intros. intro.
    eapply A3. eauto.
    eapply in_flat_map. exists (id2, fofs2, fp2). eauto. auto.
  - inv H0. red. intros. intro.
    eapply A3. eauto.
    eapply in_flat_map. exists (id1, fofs1, fp1). eauto. auto.
  - eauto.
Qed.

Lemma app_norepet_inv_tail: forall (l1 l2 l3 l4: list (positive * (block * type))) (id1: ident) (b: block) (ty1: type) id2 ty2,
    l1 ++ (id1, (b, ty1)) :: l2 = l3 ++ (id2, (b, ty2)) :: l4 ->
    ~ In b (map (fun elt : positive * (block * type) => fst (snd elt)) l1) ->
    ~ In b (map (fun elt : positive * (block * type) => fst (snd elt)) l2) ->
    ~ In b (map (fun elt : positive * (block * type) => fst (snd elt)) l3) ->
    ~ In b (map (fun elt : positive * (block * type) => fst (snd elt)) l4) ->
    id1 = id2.
Proof.
  induction l1; simpl; intros; auto.
  - destruct l3; simpl in *.
    + inv H. auto.
    + destruct p. destruct p0.
      inv H. simpl in *. eapply Decidable.not_or in H2.
      destruct H2. congruence.
  - destruct a. destruct p0.
    destruct l3; simpl in *.
    + inv H. eapply Decidable.not_or in H0.
      destruct H0. congruence.
    + inv H. simpl in *.
      eapply IHl1; eauto.
Qed.

      
Lemma footprint_norepet_env_disjoint: forall e id1 id2 b1 b2 ty1 ty2,
    list_norepet (footprint_of_env e) ->
    e ! id1 = Some (b1, ty1) ->
    e ! id2 = Some (b2, ty2) ->
    id1 <> id2 ->
    b1 <> b2.
Proof.
  intros until ty2. intros NOREP E1 E2 NEQ.
  intro. eapply NEQ. subst.
  unfold footprint_of_env in NOREP.
  generalize NOREP as NOREP1. intros.
  exploit PTree.elements_remove. eapply E1. intros (l1 & l2 & A1 & A2).  
  rewrite A1 in NOREP. rewrite map_app in NOREP. simpl in NOREP.
  exploit PTree.elements_remove. eapply E2. intros (l3 & l4 & A3 & A4).
  rewrite A3 in NOREP1. rewrite map_app in NOREP1. simpl in NOREP1.
  rewrite A1 in A3.
  eapply list_norepet_app in NOREP as (N1 & N2 & N3). inv N2.
  eapply list_norepet_app in NOREP1 as (N4 & N5 & N6). inv N5.  
  eapply app_norepet_inv_tail; eauto.
  intro. eapply N3; eauto. simpl. auto.
  intro. eapply N6; eauto. simpl. auto.
Qed.

  
Lemma footprint_norepet_fields_norepet: forall (fpl: list (ident * Z * footprint)) id fofs fp,
    list_norepet (flat_map (fun '(_, _, fp) => footprint_flat fp) fpl) ->
    In (id, fofs, fp) fpl ->
    list_norepet (footprint_flat fp).
Proof.
  induction fpl; simpl; intros; try contradiction.
  destruct a. destruct p. destruct H0.
  - inv H0. eapply list_norepet_app in H. destruct H as (A1 & A2 & A3).
    auto.
  - eapply list_norepet_app in H. destruct H as (A1 & A2 & A3).
    eauto.
Qed.


(* This lemma indicates that the footprint is a non-cyclic tree. *)
Lemma get_footprint_norepet: forall phl fp fp1,
    list_norepet (footprint_flat fp) ->
    get_footprint phl fp = Some fp1 ->
    list_norepet (footprint_flat fp1).
Proof.
  induction phl; intros until fp1; intros NOREP1 GFP; simpl in *.
  - inv GFP. auto.
  - destruct a.
    + destruct fp; try congruence.
      simpl in *. inv NOREP1.
      eapply IHphl; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      eapply IHphl. 2: eapply GFP.
      eapply footprint_norepet_fields_norepet; eauto.
    + destr_fp_enum fp ty.
      simpl in *. eauto.
Qed.


(* This lemma indicates that the footprint is a non-cyclic tree. *)
Lemma get_loc_footprint_norepet: forall phl fp b ofs b1 ofs1 fp1,
    list_norepet (footprint_flat fp) ->
    get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
    ~ In b (footprint_flat fp) ->
    list_norepet (footprint_flat fp1)
    /\ ~ In b1 (footprint_flat fp1).
Proof.
  induction phl; intros until fp1; intros NOREP1 GFP NIN; simpl in *.
  - inv GFP. auto.
  - destruct a.
    + destruct fp; try congruence.
      simpl in *. inv NOREP1.
      eapply IHphl; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      eapply IHphl. 2: eapply GFP.
      eapply footprint_norepet_fields_norepet; eauto.
      intro. eapply NIN. simpl.
      eapply in_flat_map; eauto.
    + destr_fp_enum fp ty.
      simpl in *. eauto.
Qed.

Lemma norepet_flat_fp_map_element: forall fpm id fp,
    fpm ! id = Some fp ->
    list_norepet (flat_fp_map fpm) ->
    list_norepet (footprint_flat fp).
Proof.
  intros. eapply PTree.elements_remove in H.
  destruct H as (l1 & L2 & A & B).
  unfold flat_fp_map in H0.
  rewrite A in H0.
  erewrite flat_map_app in H0. 
  eapply list_norepet_app in H0. destruct H0 as (C & D & E).
  simpl in D. eapply list_norepet_app in D. destruct D.
  auto.
Qed.

Lemma norepet_flat_fp_map_element_disjoint: forall fpm id1 id2 fp1 fp2,
    fpm ! id1 = Some fp1 ->
    fpm ! id2 = Some fp2 ->
    id1 <> id2 ->
    list_norepet (flat_fp_map fpm) ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2).
Proof.
  intros. unfold flat_fp_map in H2.
  eapply PTree.elements_correct in H.
  eapply PTree.elements_correct in H0.
  generalize dependent (PTree.elements fpm).
  induction l; intros; simpl in *; try contradiction.
  destruct a. destruct H.
  - inv H. destruct H0. inv H. try congruence.
    eapply list_norepet_app in H2 as (N1 & N2 & N3).
    simpl in *. red. intros.
    eapply N3; auto.
    eapply in_flat_map; eauto.
  - destruct H0. inv H0.
    + eapply list_norepet_app in H2 as (N1 & N2 & N3).
      simpl in *. eapply list_disjoint_sym. red. intros.
      eapply N3; auto.
      eapply in_flat_map; eauto.
    + eapply list_norepet_app in H2 as (N1 & N2 & N3).
      eauto.
Qed.

    
(** separating a footprint from the well-formed
footprint map *)
Lemma get_loc_footprint_map_norepet: forall phl id fpm b1 ofs1 fp1 e,
    list_norepet (flat_fp_map fpm) ->
    get_loc_footprint_map e (id, phl) fpm = Some (b1, ofs1, fp1) ->
    (* we require that the stack blocks and the blocks in fpm are disjoint *)
    list_disjoint (footprint_of_env e) (flat_fp_map fpm) ->
    list_norepet (footprint_flat fp1)
    /\ ~ In b1 (footprint_flat fp1).
Proof.
  intros until e. intros NOREP1 GFP DIS.
  unfold get_loc_footprint_map in GFP.
  destruct (e!id) eqn: A; try congruence.
  destruct p.
  destruct (fpm!id) eqn: B; try congruence.
  eapply get_loc_footprint_norepet; eauto.
  eapply norepet_flat_fp_map_element; eauto.
  intro. eapply DIS. eapply in_footprint_of_env; eauto.
  eapply in_footprint_flat_fp_map; eauto. auto.
Qed.  

Lemma set_footprint_incl: forall phl fp1 fp2 fp b,
    set_footprint phl fp fp1 = Some fp2 ->
    In b (footprint_flat fp2) ->
    In b (footprint_flat fp1)
    \/ In b (footprint_flat fp).
Proof.
  induction phl; simpl; intros.
  - inv H. auto.
  - destruct a.
    + destruct fp1; try congruence. 
      destruct (set_footprint phl fp fp1) eqn: A; try congruence.
      inv H. simpl in *. destruct H0; eauto.
      exploit IHphl; eauto. intros [E1|E2]; eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      destruct (set_footprint phl fp f) eqn: A; try congruence.
      inv H. simpl in *.
      exploit find_fields_split; eauto.
      intros (l1 & l2 & B1 & B2). subst.
      erewrite set_fields_split in H0; eauto. rewrite flat_map_app in *.
      simpl in *.      
      rewrite !in_app in H0.
      rewrite !in_app. destruct H0; auto.
      destruct H; auto.
      exploit IHphl; eauto. intros [E1|E2]; eauto.
    + destr_fp_enum fp1 ty.
      destruct (set_footprint phl fp fp1) eqn: A; try congruence.
      inv H. simpl in *. eauto.
Qed.
      
Lemma set_footprint_norepet: forall phl fp1 fp2 vfp,
    set_footprint phl vfp fp1 = Some fp2 ->
    list_norepet (footprint_flat fp1) ->
    list_norepet (footprint_flat vfp) ->
    list_disjoint (footprint_flat fp1) (footprint_flat vfp) ->
    list_norepet (footprint_flat fp2).
Proof.
  induction phl; intros until vfp; intros SET N1 N2 DIS; simpl in *.
  - inv SET. auto.
  - destruct a.
    + destruct fp1; try congruence. 
      destruct (set_footprint phl vfp fp1) eqn: A; try congruence.
      inv SET. simpl in *.       
      inv N1. econstructor; eauto.
      intro. exploit set_footprint_incl; eauto.
      intros [E1|E2]; try congruence.
      eapply DIS; eauto. simpl. auto.
      eapply IHphl; eauto.
      eapply list_disjoint_cons_left; eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      destruct (set_footprint phl vfp f) eqn: A; try congruence.
      inv SET. simpl in *.
      exploit IHphl; eauto.
      eapply footprint_norepet_fields_norepet; eauto.
      red. intros. eapply DIS; eauto.
      eapply in_flat_map; eauto.
      intros NF.
      exploit find_fields_split; eauto.
      intros (l1 & l2 & B1 & B2). subst.
      erewrite set_fields_split; eauto. rewrite flat_map_app in *.
      simpl in *.
      eapply list_norepet_append_commut2.
      eapply list_norepet_append_commut2 in N1.
      rewrite app_assoc in *. eapply list_norepet_app.
      eapply list_norepet_app in N1 as (N3 & N4 & N5).
      repeat apply conj; auto.
      red. intros.
      exploit set_footprint_incl; eauto. intros [E1|E2].
      eapply N5; eauto.
      eapply DIS; eauto.
      rewrite in_app in H.
      rewrite !in_app. destruct H; auto.
    + destr_fp_enum fp1 ty.
      destruct (set_footprint phl vfp fp1) eqn: A; try congruence.
      inv SET. simpl in *. eauto.
Qed.

      
(* norepet (l ++ fpm) where l is a general list which can
    represent other elements in the frame *)
Lemma set_disjoint_footprint_norepet: forall fpm1 fpm2 vfp id phl,
    list_norepet (footprint_flat vfp) ->
    list_norepet (flat_fp_map fpm1) ->
    set_footprint_map (id, phl) vfp fpm1 = Some fpm2 ->
    list_disjoint (flat_fp_map fpm1) (footprint_flat vfp) ->
    list_norepet (flat_fp_map fpm2).
Proof.
  intros until phl. intros NVFP NOREP SET DIS. simpl in *.
  destruct (fpm1 ! id) eqn: A; try congruence.
  destruct (set_footprint phl vfp f) eqn: B; try congruence. inv SET.
  (* show that f0 is norepet *)
  exploit norepet_flat_fp_map_element; eauto. intros NF.
  exploit set_footprint_norepet; eauto.
  red. intros. eapply DIS. eapply in_footprint_flat_fp_map; eauto. auto.
  intros NF0.
  unfold flat_fp_map in *.
  exploit PTree.elements_remove. eauto. intros (l1 & l2 & A1 & A2).
  exploit PTree.elements_remove. instantiate (3 := (PTree.set id f0 fpm1)).
  eapply PTree.gss; eauto. intros (l3 & l4 & A3 & A4).
  erewrite <- PTree_remove_elements_eq in A4. rewrite A2 in A4.
  rewrite A1 in *. rewrite A3 in *.  
  rewrite !flat_map_app in *. simpl in *.
  eapply list_norepet_append_commut2.
  eapply list_norepet_append_commut2 in NOREP.
  rewrite app_assoc in *. 
  rewrite <- flat_map_app in *. rewrite <- A4.
  eapply list_norepet_app in NOREP as (N1 & N2 & N3).
  eapply list_norepet_app. split. auto.
  split.
  (* f0 is norepet *)
  auto.
  (* disjointness *)
  red. intros.
  exploit set_footprint_incl; eauto.
  intros [E1|E2].
  (* x in l1 ++l2 and y in f *)
  eapply N3. auto. auto.
  (* x in l1 ++l2 and y in vfp *)
  eapply DIS.
  rewrite flat_map_app in H. eapply in_app in H.
  rewrite !in_app. destruct H; auto. auto.
Qed.

Lemma empty_footprint_flat: forall fp,
    footprint_flat (clear_footprint_rec fp) = nil.
Proof.
  induction fp using strong_footprint_ind; simpl; auto.
  induction fpl; simpl; auto.
  destruct a. destruct p. erewrite H. simpl.
  eapply IHfpl. intros. eapply H. eapply in_cons; eauto.
  econstructor. eauto.
Qed.

Lemma empty_footprint_disjoint: forall fp1 fp2,
    list_disjoint fp1 (footprint_flat (clear_footprint_rec fp2)).
Proof.
  intros. rewrite empty_footprint_flat. red. intros. inv H0.
Qed.

Lemma get_footprint_incl: forall phl fp fp1,
    get_footprint phl fp = Some fp1 ->
    incl (footprint_flat fp1) (footprint_flat fp).
Proof.
  induction phl; intros; simpl in *.
  - inv H. eapply incl_refl.
  - destruct a.
    + destruct fp; try congruence.
      simpl. red.
      intros. eapply in_cons. eapply IHphl; eauto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      simpl. red. intros. eapply in_flat_map.
      eapply IHphl in H0; eauto.
      eapply find_fields_some in FIND. destruct FIND. subst.
      exists (i, z, f). auto.
    + destruct fp; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; subst; try congruence.
      destruct list_eq_dec; subst; try congruence.
      destruct ident_eq; subst; try congruence.
      simpl. eauto.
Qed.


(* The footprint is included in the source footprint *)
Lemma get_loc_footprint_incl: forall phl fp b ofs b1 ofs1 fp1,
    get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
    incl (footprint_flat fp1) (footprint_flat fp).
Proof.
  intros. eapply get_footprint_incl.
  eapply get_loc_footprint_eq. eauto.
Qed.  

Lemma get_loc_footprint_map_incl: forall phl fpm b1 ofs1 fp1 le id,
    get_loc_footprint_map le (id, phl) fpm = Some (b1, ofs1, fp1) ->
    incl (footprint_flat fp1) (flat_fp_map fpm).
Proof.
  intros. simpl in H. destruct (le!id) in H; try congruence.
  destruct p. destruct (fpm!id) eqn: FPM; try congruence.
  red. intros. eapply get_loc_footprint_incl in H0; eauto.
  unfold flat_fp_map.
  eapply in_flat_map; eauto.
  exists (id, f). simpl. split; auto.
  eapply PTree.elements_correct. auto.
Qed.


Lemma get_loc_footprint_in: forall phl fp1 b1 ofs1 b2 ofs2 fp2,
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    In b2 (b1 :: footprint_flat fp1).
Proof.
  induction phl; intros.
  - simpl in H. inv H. econstructor; auto.
  - simpl in H. destruct a.
    + destruct fp1; try congruence.
      exploit IHphl; eauto. intros IN. inv IN.
      eapply in_cons. simpl. auto.
      eapply in_cons. simpl. auto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      exploit IHphl; eauto. intros IN. inv IN.
      econstructor. auto.
      eapply in_cons. simpl. eapply in_flat_map; eauto.
    + destr_fp_enum fp1 ty.
      exploit IHphl; eauto.
Qed.

(* The block obtained from get_loc_footprint_map comes from
   stack or the footprint map *)
Lemma get_loc_footprint_map_in_range: forall phl id fpm le b ofs fp,
    get_loc_footprint_map le (id, phl) fpm = Some (b, ofs, fp) ->
    In b (footprint_of_env le ++ flat_fp_map fpm).
Proof.
  intros. simpl in *.
  destruct (le!id) eqn: A; try congruence.
  destruct p.
  destruct (fpm!id) eqn: B; try congruence.
  exploit get_loc_footprint_in; eauto.
  intros IN. inv IN.
  eapply in_app_iff. left. eapply in_footprint_of_env; eauto.
  eapply in_app_iff. right. eapply in_footprint_flat_fp_map; eauto.
Qed.

Lemma in_app_commut {A: Type} : forall (l1 l2 l3: list A) a,
      In a (l1 ++ l2 ++ l3) <-> In a (l1 ++ l3 ++ l2).
Proof.
  intros. split; intros.
  - rewrite !in_app in *.
    repeat destruct H; auto.
  - rewrite !in_app in *.
    repeat destruct H; auto.
Qed.

Lemma set_footprint_map_incl: forall fpm1 fpm2 fp id phl b,
    set_footprint_map (id, phl) fp fpm1 = Some fpm2 ->
    In b (flat_fp_map fpm2) ->
    In b (flat_fp_map fpm1) \/ In b (footprint_flat fp).
Proof.
  intros.
  simpl in *. destruct (fpm1!id) eqn: A; try congruence.
  destruct (set_footprint phl fp f) eqn: B; try congruence.
  inv H. 
  unfold flat_fp_map in *.
  exploit PTree.elements_remove. eauto. intros (l1 & l2 & A1 & A2).
  exploit PTree.elements_remove. instantiate (3 := (PTree.set id f0 fpm1)).
  eapply PTree.gss; eauto. intros (l3 & l4 & A3 & A4).
  erewrite <- PTree_remove_elements_eq in A4. rewrite A2 in A4.
  rewrite A1 in *. rewrite A3 in *.  
  rewrite flat_map_app in *. simpl in *.
  erewrite in_app_commut in *. rewrite app_assoc in *.
  rewrite <- flat_map_app in *. rewrite A4 in *.
  rewrite in_app in *. destruct H0; auto.
  exploit set_footprint_incl; eauto. intros [E1|E2]; auto.
Qed.
  
Lemma get_set_disjoint_footprint: forall phl fp fp' fp1 fp2,
    get_footprint phl fp = Some fp1 ->
    set_footprint phl fp2 fp = Some fp' ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2) ->
    list_norepet (footprint_flat fp) ->
    list_disjoint (footprint_flat fp') (footprint_flat fp1).
Proof.
  induction phl; intros until fp2; intros GFP SFP DIS NOREP; simpl in *.
  - inv GFP. inv SFP.
    eapply list_disjoint_sym. auto.
  - destruct a.
    + destruct fp; try congruence.
      destruct (set_footprint phl fp2 fp) eqn: S1; try congruence.
      inv SFP. simpl in *.
      red. intros. inv H.
      * inv NOREP. intro. subst. eapply H2.
        eapply get_footprint_incl; eauto.
      * eapply IHphl; eauto.
        inv NOREP; auto.
    + destruct fp; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some. eapply FIND. intros (A1 & A2). subst.
      destruct (set_footprint phl fp2 f) eqn: S1; try congruence.
      inv SFP. simpl in *.
      exploit find_fields_split; eauto.
      intros (l1 & l2 & B1 & B2). subst.
      erewrite set_fields_split; eauto.
      erewrite flat_map_app in NOREP.
      eapply list_norepet_app in NOREP as (N1 & N2 & N3).
      red. intros.
      rewrite flat_map_app in H.
      eapply in_app_iff in H. destruct H.
      * eapply N3. eauto.
        simpl. eapply in_app. left.
        eapply get_footprint_incl; eauto.
      * simpl in H. eapply in_app in H.
        destruct H.
        (* adhoc *)
        -- eapply IHphl; eauto.
           simpl in N2. eapply list_norepet_append_left. eauto.
        -- simpl in N2.
           eapply list_norepet_app in N2 as (N4 & N5 & N6).
           intro. subst. eapply N6; eauto.
           eapply get_footprint_incl; eauto.
    + destr_fp_enum fp ty.
      destruct (set_footprint phl fp2 fp) eqn: S1; try congruence.
      inv SFP. simpl in *. eapply IHphl; eauto.
Qed.

(* Set a footprint also remove the original one out. This removed
   footprint is disjoint with the updated footprint map *)
Lemma get_set_disjoint_footprint_map: forall l i fpm1 fpm2 b ofs fp1 fp2 le,
    get_loc_footprint_map le (i, l) fpm1 = Some (b, ofs, fp1) ->
    set_footprint_map (i, l) fp2 fpm1 = Some fpm2 ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2) ->
    list_norepet (flat_fp_map fpm1) ->
    list_disjoint (flat_fp_map fpm2) (footprint_flat fp1).
Proof.
  intros. simpl in *.
  destruct (le ! i) eqn: A1; try congruence. destruct p.
  destruct (fpm1 ! i) eqn: A2; try congruence.
  destruct (set_footprint l fp2 f) eqn: A3; try congruence. inv H0.
  red. intros.
  eapply in_flat_map in H0.
  destruct H0 as ((id & fp) & IN1 & IN2). 
  eapply PTree.elements_complete in IN1. rewrite PTree.gsspec in IN1.
  destruct peq in IN1.
  - inv IN1.
    eapply get_set_disjoint_footprint; eauto.
    eapply get_loc_footprint_eq; eauto.
    eapply norepet_flat_fp_map_element; eauto.
  - eapply norepet_flat_fp_map_element_disjoint. eapply IN1. eapply A2.
    auto. auto. auto.
    eapply get_loc_footprint_incl; eauto.
Qed.      
    
Lemma get_clear_footprint_incl1: forall phl fp1 fp2 fp3,
    get_footprint phl fp1 = Some fp2 ->
    set_footprint phl (clear_footprint_rec fp2) fp1 = Some fp3 ->
    incl (footprint_flat fp2 ++ footprint_flat fp3) (footprint_flat fp1).
Proof.
  intros. red. intros.
 eapply in_app_iff in H1. destruct H1.
 eapply get_footprint_incl; eauto.
 exploit set_footprint_incl; eauto.
 intros [A|B]; auto.
 rewrite empty_footprint_flat in B. inv B.
Qed.


Lemma get_clear_footprint_incl2: forall phl fp1 fp2 fp3,
    get_footprint phl fp1 = Some fp2 ->
    set_footprint phl (clear_footprint_rec fp2) fp1 = Some fp3 ->
    incl (footprint_flat fp1) (footprint_flat fp2 ++ footprint_flat fp3).
Proof.
  induction phl; simpl in *; intros.
  - inv H0. inv H. rewrite empty_footprint_flat. rewrite app_nil_r.
    eapply incl_refl.
  - destruct a.
    + destruct fp1; try congruence.
      destruct (set_footprint phl (clear_footprint_rec fp2) fp1) eqn: A; try congruence.
      inv H0. 
      generalize (IHphl fp1 fp2 f H A). intros INCL1.
      red. simpl. intros. destruct H0; subst.
      * eapply in_app_iff. right. econstructor. auto.
      * eapply INCL1 in H0. eapply in_app_iff in H0. destruct H0.
        eapply in_app_iff; eauto.
        eapply in_app_iff. right. eapply in_cons; auto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      destruct (set_footprint phl (clear_footprint_rec fp2) f) eqn: A; try congruence.
      inv H0. 
      exploit find_fields_some; eauto. intros (B1 & B2). subst.
      generalize (IHphl f fp2 f0 H A). intros INCL1.
      red. simpl. intros.
      eapply in_flat_map in H0. destruct H0 as (((fid & fofs) & ffp) & IN1 & IN2).
      exploit find_fields_split; eauto. intros (l1 & l2 & A1 & A2). subst.
      erewrite set_fields_split; eauto.
      rewrite flat_map_app. simpl. rewrite !in_app. rewrite !in_app in IN1.
      destruct IN1.
      * right. left. eapply in_flat_map; eauto.
      * inv H0.
        -- inv H1. eapply INCL1 in IN2.
           eapply in_app in IN2. destruct IN2; auto.
        -- repeat right. eapply in_flat_map; eauto.
    + destr_fp_enum fp1 ty.
      destruct (set_footprint phl (clear_footprint_rec fp2) fp1) eqn: A; try congruence.
      inv H0. simpl. eauto.
Qed.

Lemma get_clear_footprint_equiv: forall phl fp1 fp2 fp3,
    get_footprint phl fp1 = Some fp2 ->
    set_footprint phl (clear_footprint_rec fp2) fp1 = Some fp3 ->
    list_equiv (footprint_flat fp2 ++ footprint_flat fp3) (footprint_flat fp1).
Proof.
  intros. split.
  eapply get_clear_footprint_incl1; eauto.
  eapply get_clear_footprint_incl2; eauto.
Qed.


(* (fpm\fp ) * fp = fpm: this lemma relies on wf_env so we put here *)
Lemma get_clear_footprint_map_equiv: forall fpm1 fpm2 fp le id phl b ofs,
    get_loc_footprint_map le (id, phl) fpm1 = Some (b, ofs, fp) ->
    clear_footprint_map le (id, phl) fpm1 = Some fpm2 ->
    list_equiv (footprint_flat fp ++ flat_fp_map fpm2) (flat_fp_map fpm1).
Proof.
  intros until ofs. intros GFP CLR.
  unfold clear_footprint_map in CLR. rewrite GFP in CLR.
  split.   
  - intros. eapply in_app_iff in H. destruct H.
    + eapply get_loc_footprint_map_incl; eauto.
    + exploit set_footprint_map_incl; eauto.
      rewrite empty_footprint_flat. simpl. intros [A|B]; try inv B; auto.
  - intros IN.
    simpl in *. destruct (le ! id) eqn: A1; try congruence.
    destruct p.
    destruct (fpm1 ! id) eqn: A2; try congruence.
    destruct (set_footprint phl (clear_footprint_rec fp) f) eqn: A3; try congruence.
    inv CLR.
    generalize GFP as GFP1. intros. eapply get_loc_footprint_eq in GFP1.
    generalize (get_clear_footprint_equiv _ _ _ _ GFP1 A3). intros EQV.
    eapply in_flat_map in IN as ((id1 & fp2) & IN3 & IN4).
    simpl in *. eapply PTree.elements_complete in IN3.
    destruct (ident_eq id id1).
    + subst. rewrite A2 in IN3. inv IN3.
      eapply EQV in IN4. eapply in_app_iff in IN4. destruct IN4.
      * eapply in_app; auto.
      * eapply in_app_iff.
        right.
        eapply in_flat_map; eauto.
        exists (id1, f0). split; eauto.
        eapply PTree.elements_correct. eapply PTree.gss.
    + eapply in_app. right.
      eapply in_flat_map; eauto.
      exists (id1, fp2). split; eauto.
      eapply PTree.elements_correct. erewrite PTree.gso; eauto.
Qed.


(** ** Typing of the footprint: used to make sure the footprint is well-formed *)

Section COMP_ENV.

Variable ce: composite_env.

(* Definition of wt_footprint (well-typed footprint). Intuitively, it
says that the footprint is an abstract form of the syntactic type
ty. We need an intermediate composite_env to act as the recursive
guard to simulate the move checking because we do not allow unbounded
appearence of shallow struct. What if we allow recursive struct in the
footprint but if can be rule out in move checking? *)
Inductive wt_footprint : type -> footprint -> Prop :=
| wt_fp_emp: forall ty
    (* It means that the location with this type is not
        initialized or this location is scalar type *)
    (WF: forall orgs id, ty <> Tstruct orgs id),
    wt_footprint ty fp_emp
| wt_fp_scalar: forall ty
    (WF: scalar_type ty = true),
    wt_footprint ty (fp_scalar ty)
| wt_fp_struct: forall orgs id fpl co
    (CO: ce ! id = Some co)
    (STRUCT: co_sv co = Struct)
    (** TODO: combine WT1 andp WT2 elegantly. WT1 is used in getting
    the sub-field's footprint. WT2 is used in proving the properties
    of sub-field's footprint *)
    (WT1: forall fid fty,
        field_type fid co.(co_members) = OK fty ->
        (* For simplicity, use find_field instead of In predicate *)
        exists ffp fofs,
          find_fields fid fpl = Some (fid, fofs, ffp)
          /\ field_offset ce fid co.(co_members) = OK fofs
          (* bound condition *)
          /\ wt_footprint fty ffp)
    (WT2: forall fid fofs ffp,
        find_fields fid fpl = Some (fid, fofs, ffp) ->
        exists fty,
          field_type fid co.(co_members) = OK fty
          /\ field_offset ce fid co.(co_members) = OK fofs
          /\ wt_footprint fty ffp)
    (* make sure that the flattened footprint list has the same order
    as that of the members *)
    (FLAT: name_footprints fpl = name_members (co_members co)),
    (* This norepet property is used to ensure that set_field onlys
    update one footprint instead of overriding some footprint with the
    same name *)
    (* (NOREP: list_norepet (name_footprints fpl)), *)
    wt_footprint (Tstruct orgs id) (fp_struct id fpl)
| wt_fp_enum: forall orgs id tagz fid fty fofs fp co
    (CO: ce ! id = Some co)
    (ENUM: co_sv co = TaggedUnion)
    (TAG: list_nth_z co.(co_members) tagz = Some (Member_plain fid fty))
    (* avoid some norepet properties *)
    (FTY: field_type fid co.(co_members) = OK fty)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (WT: wt_footprint fty fp),
    wt_footprint (Tvariant orgs id) (fp_enum id orgs tagz fid fofs fp)
| wt_fp_box: forall ty b fp
    (* this is ensured by bm_box *)
    (WT: wt_footprint ty fp),
    (* It is used to make sure that dropping any location within a
    block does not cause overflow *)
    wt_footprint (Tbox ty) (fp_box b (sizeof ce ty) fp).

Definition wt_footprint_list tyl fpl :=
  list_forall2 wt_footprint tyl fpl.

End COMP_ENV.


(* The definition of wt_path should be a function instead of a
relation. *)
Inductive wt_path ce (ty: type) : list path -> type -> Prop :=
| wt_path_nil: wt_path ce ty nil ty
| wt_path_deref: forall phl ty1 ty2
    (WP1: wt_path ce ty phl ty1)
    (WP2: type_deref ty1 = OK ty2),
    wt_path ce ty (phl ++ [ph_deref]) ty2
| wt_path_field: forall phl orgs id co ty1 fid
    (WP1: wt_path ce ty phl (Tstruct orgs id))
    (WP2: ce ! id = Some co)
    (WP3: field_type fid (co_members co) = OK ty1)
    (WP4: co_sv co = Struct),
    wt_path ce ty (phl++[ph_field fid]) ty1
| wt_path_downcast: forall phl orgs id co ty1 fid
    (WP1: wt_path ce ty phl (Tvariant orgs id))
    (WP2: ce ! id = Some co)
    (WP3: field_type fid (co_members co) = OK ty1)
    (WP4: co_sv co = TaggedUnion),
    wt_path ce ty (phl++[ph_downcast (Tvariant orgs id) fid]) ty1
.

Lemma wt_path_nil_inv: forall ce ty1 ty2,
    wt_path ce ty1 nil ty2 ->
    ty1 = ty2.
Proof.
  intros. inv H. auto.
  1-3: destruct phl; inv H1.
Qed.

Lemma wt_path_deref_inv: forall ce ty1 ty2 phl,
    wt_path ce ty1 (phl ++ [ph_deref]) ty2 ->
    exists ty1', wt_path ce ty1 phl ty1'
            /\ type_deref ty1' = OK ty2.
Proof.
  intros. inv H.
  destruct phl; inv H1.
  eapply app_inj_tail in H1. destruct H1. subst. eauto.
  eapply app_inj_tail in H1. destruct H1. congruence.
  eapply app_inj_tail in H1. destruct H1. congruence.
Qed.

Lemma wt_path_field_inv: forall ce ty1 ty2 phl fid,
    wt_path ce ty1 (phl ++ [ph_field fid]) ty2 ->
    exists id orgs co,
      wt_path ce ty1 phl (Tstruct orgs id)
      /\ ce ! id = Some co
      /\ field_type fid (co_members co) = OK ty2
      /\ co_sv co = Struct.
Proof.
  intros. inv H.
  destruct phl; inv H1.
  eapply app_inj_tail in H1. destruct H1. congruence.
  eapply app_inj_tail in H1. destruct H1. inv H0.
  exists id, orgs, co. eauto.
  eapply app_inj_tail in H1. destruct H1. congruence.
Qed.

Lemma wt_path_downcast_inv: forall ce ty1 ty2 phl fid ty,
    wt_path ce ty1 (phl ++ [ph_downcast ty fid]) ty2 ->
    exists id orgs co,
      ty = Tvariant orgs id                    
      /\ wt_path ce ty1 phl (Tvariant orgs id)
      /\ ce ! id = Some co
      /\ field_type fid (co_members co) = OK ty2
      /\ co_sv co = TaggedUnion.
Proof.
  intros. inv H.
  destruct phl; inv H1.
  eapply app_inj_tail in H1. destruct H1. congruence.
  eapply app_inj_tail in H1. destruct H1. congruence.
  eapply app_inj_tail in H1. destruct H1. inv H0.
  exists id, orgs, co. eauto.
Qed.


Lemma wt_path_det: forall phl ty1 ty2 ty3 ce,
    wt_path ce ty1 phl ty2 ->
    wt_path ce ty1 phl ty3 ->
    ty2 = ty3.
Proof.
  intro phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst.
    eapply wt_path_nil_inv in H0. subst.
    eapply wt_path_nil_inv in H. subst. auto.
  - eapply length_S_inv in LEN.
    destruct LEN as (l' & a & A & LEN). subst.
    destruct a.
    + eapply wt_path_deref_inv in H0.
      destruct H0 as (ty1' & A1 & A2).
      eapply wt_path_deref_inv in H.
      destruct H as (ty1'' & A3 & A4).
      exploit IHn. eauto. eapply A1. eapply A3. intros.
      subst. rewrite A2 in A4. inv A4. auto.
    + eapply wt_path_field_inv in H0 as (id & orgs & co & A1 & A2 & A3 & A4).
      eapply wt_path_field_inv in H as (id1 & orgs1 & co1 & B1 & B2 & B3 & B4).
      exploit IHn. eauto. eapply A1. eapply B1.
      intros. inv H. rewrite A2 in B2. inv B2. rewrite A3 in B3. inv B3.
      auto.
    + eapply wt_path_downcast_inv in H0 as (id & orgs & co & A1 & A2 & A3 & A4 & A5).
      eapply wt_path_downcast_inv in H as (id1 & orgs1 & co1 & B1 & B2 & B3 & B4 & B5).
      rewrite A1 in B1. inv B1.
      rewrite A3 in B3. inv B3. rewrite A4 in B4. inv B4. auto.
Qed.

      
Lemma wt_path_app: forall phl2 phl1 ty1 ty2 ty3 ce,
    wt_path ce ty1 phl1 ty2 ->
    wt_path ce ty1 (phl1 ++ phl2) ty3 ->
    wt_path ce ty2 phl2 ty3.
Proof.
  intro phl2. cut (exists n, length phl2 = n); eauto. intros (n & LEN).
  generalize dependent phl2.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst.
    rewrite app_nil_r in H0. exploit wt_path_det. eapply H. eapply H0.
    intro. subst. econstructor.
  - eapply length_S_inv in LEN.
    destruct LEN as (l' & a & A & LEN). subst.
    destruct a.
    + rewrite app_assoc in H0.
      eapply wt_path_deref_inv in H0.
      destruct H0 as (ty1' & A1 & A2).
      econstructor. eapply IHn; eauto. auto.
    + rewrite app_assoc in H0.
      eapply wt_path_field_inv in H0 as (id & orgs & co & A1 & A2 & A3 & A4).
      econstructor; eauto.
    + rewrite app_assoc in H0.
      eapply wt_path_downcast_inv in H0 as (id & orgs & co & A1 & A2 & A3 & A4 & A5).
      subst.
      econstructor; eauto.
Qed.

Lemma wt_path_app_inv: forall phl2 phl1 ty1 ty3 ce,
    wt_path ce ty1 (phl1 ++ phl2) ty3 ->
    exists ty2,
      wt_path ce ty1 phl1 ty2
      /\ wt_path ce ty2 phl2 ty3.
Proof.
  intro phl2. cut (exists n, length phl2 = n); eauto. intros (n & LEN).
  generalize dependent phl2.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst.
    rewrite app_nil_r in H.
    exists ty3. split; auto. econstructor.
  - eapply length_S_inv in LEN.
    destruct LEN as (l' & a & A & LEN). subst.
    destruct a.
    + rewrite app_assoc in H.
      eapply wt_path_deref_inv in H.
      destruct H as (ty1' & A1 & A2).
      exploit IHn; eauto. intros (ty2' & B1 & B2).
      exists ty2'. split; auto.
      econstructor; eauto.
    + rewrite app_assoc in H.
      eapply wt_path_field_inv in H as (id & orgs & co & A1 & A2 & A3 & A4).
      exploit IHn; eauto. intros (ty2' & B1 & B2).
      exists ty2'. split; auto.
      econstructor; eauto.
    + rewrite app_assoc in H.
      eapply wt_path_downcast_inv in H as (id & orgs & co & A1 & A2 & A3 & A4 & A5).
      subst.
      exploit IHn; eauto.
      intros (ty2' & B1 & B2).
      exists ty2'. split; auto.
      econstructor; eauto.
Qed.



Lemma wt_place_wt_path: forall p e ce id l ty b,
    wt_place (env_to_tenv e) ce p ->
    path_of_place p = (id, l) ->
    e ! id = Some (b, ty) ->
    wt_path ce ty l (typeof_place p).
Proof.
  induction p; simpl; intros.
  - inv H0. inv H.
    unfold env_to_tenv in WT1.
    rewrite PTree.gmap1 in WT1. rewrite H1 in WT1. inv WT1.
    constructor.
  - destruct (path_of_place p) eqn: POP. inv H0.
    inv H. econstructor; eauto.
    rewrite <- WT2. eauto.
    (** TODO: update field_type in wt_path  *)
    admit.
  - destruct (path_of_place p) eqn: POP. inv H0.
    inv H. econstructor; eauto.
  - destruct (path_of_place p) eqn: POP. inv H0.
    inv H. rewrite WT2. econstructor; eauto.
    rewrite <- WT2. eauto.    
    (** TODO: update field_type in wt_path  *)
    admit.
Admitted.

(** IMPORTANT TODO *)
Lemma get_wt_footprint_wt: forall phl ty1 ty2 ce (WTPH: wt_path ce ty1 phl ty2) fp1 fp2,
    wt_footprint ce ty1 fp1 ->
    get_footprint phl fp1 = Some fp2 ->
    wt_footprint ce ty2 fp2.
Proof.
  induction 1; intros; simpl in *.
  - inv H0. auto.
  - exploit get_footprint_app_inv; eauto.
    intros (fp3 & A1 & A2). simpl in A2. destruct fp3; try congruence.
    inv A2. exploit IHWTPH; eauto.
    intros A2. inv A2. simpl in WP2. inv WP2. auto.
  - exploit get_footprint_app_inv; eauto.
    intros (fp3 & A1 & A2). simpl in A2. destruct fp3; try congruence.
    destruct (find_fields fid fpl) eqn: FIND; try congruence.
    repeat destruct p. inv A2.
    exploit IHWTPH; eauto. intros A3. inv A3.
    exploit find_fields_some; eauto.
    intros (B1 & B2). subst.
    exploit WT2; eauto.
    intros (fty & C1 & C2 & C3).
    rewrite WP2 in CO. inv CO.
    rewrite WP3 in C1. inv C1.
    auto.
  - exploit get_footprint_app_inv; eauto.
    intros (fp3 & A1 & A2). simpl in A2. destruct fp3; try congruence.
    destruct ident_eq in A2; try congruence.
    destruct list_eq_dec in A2; try congruence.
    destruct ident_eq in A2; try congruence.
    inv A2.
    exploit IHWTPH; eauto. intros A3. inv A3.
    rewrite WP2 in CO. inv CO.
    rewrite WP3 in FTY. inv FTY. auto.
Qed.    
    
(* A well typed footprint can imply all the sub-footprint's
well-typedness and the path to htis footprint also is well-typed *) 
Lemma get_wt_footprint_exists_wt: forall phl fp fp1 ty ce,
    wt_footprint ce ty fp ->
    get_footprint phl fp = Some fp1 ->
    exists ty1, wt_footprint ce ty1 fp1
           /\ wt_path ce ty phl ty1.
Proof.
  intros phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst.
    simpl in *. inv H0.
    exists ty. split; eauto.
    econstructor.
  - exploit length_S_inv; eauto.
    intros (phl' & a & TYS & LEN1). subst.
    exploit get_footprint_app_inv. eauto.
    intros (fp3 & G1 & G2).
    simpl in G2.
    destruct a.
    + destruct fp3; try congruence.
      inv G2. exploit IHn; eauto.
      intros (ty1 & A1 & A2).
      inv A1.
      exists ty0. split; auto. econstructor; eauto.      
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: A; try congruence.
      repeat destruct p.
      inv G2.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      exploit IHn; eauto. intros (ty1 & W1 & W2).
      inv W1.      
      exploit WT2; eauto.
      intros (fty & B1 & B2 & B3).
      exists fty. split; auto.
      econstructor; eauto. 
    + destruct fp3; try congruence.
      destruct ty0; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence. subst.
      inv G2. exploit IHn; eauto.
      intros (ty1 & A1 & A2).
      inv A1. exists fty. split; auto.
      econstructor; eauto.
Qed.
      
Lemma get_loc_footprint_map_different_local: forall id1 id2 phl1 phl2 fpm e b1 b2 ofs1 ofs2 fp1 fp2,
    list_norepet (footprint_of_env e ++ flat_fp_map fpm) ->
    id1 <> id2 ->
    get_loc_footprint_map e (id1, phl1) fpm = Some (b1, ofs1, fp1) ->
    get_loc_footprint_map e (id2, phl2) fpm = Some (b2, ofs2, fp2) ->
    b1 <> b2 /\ ~ In b1 (footprint_flat fp2) /\ ~ In b2 (footprint_flat fp1).
Proof.
  intros until fp2. intros NOREP NEQ GFP1 GFP2.
  simpl in *.
  destruct (e!id1) eqn: A1; try congruence. destruct p.
  destruct (e!id2) eqn: A2; try congruence. destruct p.
  destruct (fpm!id1) eqn: B1; try congruence. 
  destruct (fpm!id2) eqn: B2; try congruence.
  exploit get_loc_footprint_in. eapply GFP1. intros IN1.
  exploit get_loc_footprint_in. eapply GFP2. intros IN2.
  eapply list_norepet_app in NOREP as (N1 & N2 & N3).
  inv IN1; inv IN2.  
  - repeat apply conj.
    + eapply footprint_norepet_env_disjoint; eauto.
    + intro. eapply N3.
      eapply in_footprint_of_env. eapply A1.
      eapply in_footprint_flat_fp_map. eapply B2.
      eapply get_loc_footprint_incl. eapply GFP2. eapply H. auto.
    + intro. eapply N3.
      eapply in_footprint_of_env. eapply A2.
      eapply in_footprint_flat_fp_map. eapply B1.
      eapply get_loc_footprint_incl. eauto. eauto. auto.
  - repeat apply conj.
    + eapply N3.
      eapply in_footprint_of_env. eauto.
      eapply in_footprint_flat_fp_map. eapply B2. auto.
    + intro. eapply N3.
      eapply in_footprint_of_env. eapply A1.
      eapply in_footprint_flat_fp_map. eapply B2.
      eapply get_loc_footprint_incl. eauto. eauto. auto.
    + intro.
      eapply norepet_flat_fp_map_element_disjoint.
      eapply B1. eapply B2. eauto. auto.
      eapply get_loc_footprint_incl; eauto. eauto. auto.
  - repeat apply conj.
    + intro. subst. eapply N3.
      eapply in_footprint_of_env. eapply A2.
      eapply in_footprint_flat_fp_map. eapply B1. eauto. auto.
    + intro. eapply norepet_flat_fp_map_element_disjoint.      
      eapply B1. eapply B2. eauto. auto. eauto.
      eapply get_loc_footprint_incl; eauto. eauto. 
    + intro.
      eapply N3.
      eapply in_footprint_of_env. eapply A2.
      eapply in_footprint_flat_fp_map. eapply B1.
      eapply get_loc_footprint_incl. eauto. eauto. auto.
  - repeat apply conj.
    + intro. subst.
      eapply norepet_flat_fp_map_element_disjoint.      
      eapply B1. eapply B2. eauto. auto. eauto. eauto. auto.
    + intro.
      eapply norepet_flat_fp_map_element_disjoint.      
      eapply B1. eapply B2. eauto. auto. eauto.
      eapply get_loc_footprint_incl. eauto. eauto. auto.
    + intro.
      eapply norepet_flat_fp_map_element_disjoint.      
      eapply B1. eapply B2. eauto. auto.
      eapply get_loc_footprint_incl. eauto. eauto. eauto. auto.
Qed.

(** Properties of getting the footprint in disjoint paths *)

Section COMP_ENV.

Variable ce : composite_env.

Hypothesis CONSISTENT: composite_env_consistent ce.

Hypothesis COMP_RANGE: forall id co, ce ! id = Some co -> co_sizeof co <= Ptrofs.max_unsigned.
Hypothesis COMP_LEN: forall id co, ce ! id = Some co -> list_length_z (co_members co) <= Int.max_unsigned.
Hypothesis COMP_NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)).


(* The field type must be in the range of the struct it resides
in. This lemma require consistent composite because the size of the
struct is computed by co_sizeof instead of sizeof_struct *)
Lemma field_offset_in_range_complete: forall ce co id ofs ty,
    co_sv co = Struct ->
    composite_consistent ce co ->
    field_offset ce id (co_members co) = OK ofs ->
    field_type id (co_members co) = OK ty ->
    0 <= ofs /\ ofs + sizeof ce ty <= co_sizeof co.
Proof.
  intros.
  exploit field_offset_in_range; eauto.
  intros (S1 & S2). 
  split. lia.
  (* to show that sizeof_struct ce co0 <= co_sizeof co0 *)
  erewrite co_consistent_sizeof; eauto.
  erewrite co_consistent_alignof; eauto.
  rewrite H. simpl.
  generalize (sizeof_composite_pos ce0 Struct (co_members co)). simpl.
  generalize (alignof_composite_pos ce0 (co_members co) Struct).
  intros M1 M2. simpl in M1.
  generalize (align_le (sizeof_struct ce0 (co_members co)) _ M1).
  intros M3. lia.
Qed.

Lemma variant_field_offset_in_range_complete: forall ce co id ofs ty,
    co_sv co = TaggedUnion ->
    composite_consistent ce co ->
    variant_field_offset ce id (co_members co) = OK ofs ->
    field_type id (co_members co) = OK ty ->
    4 <= ofs /\ ofs + sizeof ce ty <= co_sizeof co.
Proof.
  intros.
  exploit variant_field_offset_in_range; eauto.
  intros (S1 & S2). 
  split. lia.
  (* to show that sizeof_struct ce co0 <= co_sizeof co0 *)
  erewrite co_consistent_sizeof; eauto.
  erewrite co_consistent_alignof; eauto.
  rewrite H. simpl.
  generalize (sizeof_composite_pos ce0 TaggedUnion (co_members co)). simpl.
  generalize (alignof_composite_pos ce0 (co_members co) TaggedUnion).
  intros M1 M2. simpl in M1.
  generalize (align_le (sizeof_variant ce0 (co_members co)) _ M1).
  intros M3. lia.
Qed.


(* Two memory location (b1, ofs1) and (b2, ofs2) which have type ty1
and ty2 are non-overlap *)
Definition loc_disjoint (b1 b2: block) (ty1 ty2: type) (ofs1 ofs2: Z) : Prop :=
  b1 <> b2 \/ ofs2 + sizeof ce ty2 <= ofs1 \/ ofs1 + sizeof ce ty1 <= ofs2.


(** The memory location obtained from get_loc_footprint is either in
    the range of [(b, ofs), (b, ofs+ sizeof ty)] or in the footprint
    fp. Maybe this lemma require norepet of fp? Because
    get_loc_footprint_disjoint_loc need this. *)
Lemma get_loc_footprint_in_range: forall phl fp b ofs b1 ofs1 fp1 ty ty1,
    wt_footprint ce ty fp ->
    wt_path ce ty phl ty1 ->
    ~ In b (footprint_flat fp) ->
    (* no cycle in the footprint *)
    list_norepet (footprint_flat fp) ->
    get_loc_footprint phl fp b ofs = Some (b1, ofs1, fp1) ->
    (b = b1 /\ ofs <= ofs1 /\ ofs1 + sizeof ce ty1 <= ofs + sizeof ce ty)
    \/ (b <> b1 /\ In b1 (footprint_flat fp)).
Proof.
  intro phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros until ty1; intros WTFP WTPH NIN NOREP GFP; simpl in *.  
  - eapply length_zero_iff_nil in LEN. subst. simpl in *.
    inv GFP. eapply wt_path_nil_inv in WTPH. subst. left.
    split; auto. lia.    
  - eapply length_S_inv in LEN. destruct LEN as (phl' & ph & APP & LEN).
    subst. 
    exploit get_loc_footprint_app_inv. eauto.
    intros (b2 & ofs2 & fp3 & A1 & A2).
    simpl in A2.
    destruct ph.
    + destruct fp3; try congruence.
      eapply wt_path_deref_inv in WTPH as (ty' & WTPH & TYDEF).
      eapply type_deref_some in TYDEF. subst.
      inv A2.
      exploit get_loc_footprint_norepet; eauto.
      simpl. intros (C1 & C2). eapply Decidable.not_or in C2. destruct C2 as (C2 & C3).
      exploit IHn. eauto. eapply WTFP. eauto. eauto. eauto. eauto.
      intros [B1 | B2].
      * destruct B1. subst.
        right. split; auto.
        eapply get_loc_footprint_incl; eauto. simpl. auto.
      * destruct B2. right. split.
        intro. subst. eapply NIN. eapply get_loc_footprint_incl. eapply A1. 
        simpl. auto.
        eapply get_loc_footprint_incl. eapply A1. simpl. auto.
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      inv A2. eapply wt_path_field_inv in WTPH as (id1 & orgs & co & WTPH & CO & FTY & STRUCT).
      exploit find_fields_some; eauto. intros (C1 & C2). subst.
      exploit get_loc_footprint_norepet. eauto. eapply A1. auto.
      intros (N1 & N2).
      exploit get_wt_footprint_wt. eauto. eapply WTFP. eapply get_loc_footprint_eq. eauto.
      intros WTFP1. inv WTFP1.
      exploit WT2; eauto. intros (fty & FTY1 & FOFS & WTFP2). 
      rewrite CO in CO0. inv CO0.
      rewrite FTY in FTY1. inv FTY1.
      exploit IHn. eauto. eapply WTFP. all: eauto.
      intros [B1 | B2].
      * destruct B1. subst.
        left. split; auto.
        simpl in H0. rewrite CO in H0.
        exploit field_offset_in_range_complete; eauto. lia.
      * destruct B2. right. split; auto.
    + destr_fp_enum fp3 ty0.
      inv A2.
      eapply wt_path_downcast_inv in WTPH as (id1 & orgs1 & co & TY & WTPH & CO & FTY & ENUM).
      inv TY.
      exploit get_loc_footprint_norepet. eauto. eapply A1. auto.
      intros (N1 & N2).      
      exploit get_wt_footprint_wt. eauto. eapply WTFP. eapply get_loc_footprint_eq. eauto.
      intros WTFP1. inv WTFP1.
      rewrite CO in CO0. inv CO0. rewrite FTY in FTY0. inv FTY0.
      exploit IHn. eauto. eapply WTFP. all: eauto.
      intros [B1 | B2].
      * destruct B1. subst.
        left. split; auto.
        simpl in H0. rewrite CO in H0.
        exploit variant_field_offset_in_range_complete; eauto. lia.
      * destruct B2. right. split; auto.
Qed.

(** IMPORTANT TODO: This lemma says that the (memory locations,
   footprint) obtained from different location are different, no
   matter what paths it resides in. *)
Lemma get_loc_footprint_disjoint_loc: forall phl1 phl2 b1 b2 ty1 ty2 ofs1 ofs2 b1' b2' ofs1' ofs2' ty1' ty2' fp1 fp2 fp1' fp2',
    loc_disjoint b1 b2 ty1 ty2 ofs1 ofs2 ->
    (* What relation between ty1 and ty1'?? We can prove sizeof
          ty1 = sizeof ty1'*)
    wt_footprint ce ty1 fp1 ->
    wt_footprint ce ty2 fp2 ->
    wt_path ce ty1 phl1 ty1' ->
    wt_path ce ty2 phl2 ty2' ->
    get_loc_footprint phl1 fp1 b1 ofs1 = Some (b1', ofs1', fp1') ->
    get_loc_footprint phl2 fp2 b2 ofs2 = Some (b2', ofs2', fp2') ->
    list_disjoint (footprint_flat fp1) (footprint_flat fp2) ->
    list_norepet (footprint_flat fp1) ->
    list_norepet (footprint_flat fp2) ->
    ~ In b1 (footprint_flat fp1) ->
    ~ In b2 (footprint_flat fp2) ->
    ~ In b1 (footprint_flat fp2) ->
    ~ In b2 (footprint_flat fp1) ->
    loc_disjoint b1' b2' ty1' ty2' ofs1' ofs2'
    /\ ~ In b1' (footprint_flat fp2')
    /\ ~ In b2' (footprint_flat fp1')
    /\ list_disjoint (footprint_flat fp1') (footprint_flat fp2').
Proof.
  induction phl1; intros until fp2'; intros DIS1 WT1 WT2 WTPH1 WTPH2 G1 G2 DIS2 NOREP1 NOREP2 IN1 IN2 IN3 IN4.
  - simpl in G1. inv G1.
    exploit get_loc_footprint_in_range. eapply WT2. eapply WTPH2. 
    3: eapply G2. eauto. eauto.
    intros [[A1 [A2 A3]]|[A1 A2]].
    + subst. repeat apply conj.
      * destruct DIS1; red; auto.
        right. 
        generalize sizeof_pos. intros.
        destruct H. lia.
        eapply wt_path_nil_inv in WTPH1. subst. lia.
      * intro. apply IN3.
        eapply get_loc_footprint_incl; eauto.
      * auto.  
      * red. intros. intro.
        eapply DIS2. eauto. eapply get_loc_footprint_incl; eauto.
        auto.
    + repeat apply conj.
      * red. left.
        intro. subst. congruence.
      * intro. apply IN3.
        eapply get_loc_footprint_incl; eauto.
      * intro. eapply DIS2; eauto.
      * red. intros. intro.
        eapply DIS2. eauto. eapply get_loc_footprint_incl; eauto.
        auto.
  - replace (a::phl1) with ((a::nil) ++ phl1) in G1 by auto.
    exploit get_loc_footprint_app_inv. eauto.
    intros (b3 & ofs3 & fp3 & B1 & B2).
    (* show fp3 is well-typed *)
    exploit get_wt_footprint_exists_wt. eapply WT1.
    eapply get_loc_footprint_eq; eauto.
    intros (ty3 & C1 & C2).
    (* show (b3, ofs3) has no overlap with (b2,ofs2) *)
    assert (DIS3: loc_disjoint b3 b2 ty3 ty2 ofs3 ofs2).
    { exploit get_loc_footprint_in_range. eapply WT1. eapply C2.
      3: eapply B1. eauto.
      eauto. intros [[A1 [A2 A3]]|[A1 A2]].
      - subst. 
        destruct DIS1; red; auto.
        right. 
        generalize sizeof_pos. intros.
        destruct H. lia. lia.
      - red. left.
        intro. subst. congruence. }
    exploit get_loc_footprint_norepet. 2: eapply B1. eauto. eauto.
    intros (D1 & D2).
    eapply IHphl1.
    eapply DIS3. 1-6: eauto.
    eapply wt_path_app. eauto. simpl. auto.
    (* disjointness between fp3 and fp2 *)
    red. intros. intro. eapply DIS2.
    eapply get_loc_footprint_incl; eauto. eauto. auto.
    eauto. eauto.
    (* four notin *)
    eauto. eauto.
    (* prove b3 is not in fp2 *)
    exploit get_loc_footprint_in_range. eapply WT1. eapply C2. 
    eapply IN1. eauto. eauto.
    intros [[A1 [A2 A3]]|[A1 A2]].
    subst. eauto.
    intro. eapply DIS2. eauto. eauto. auto.
    (* b2 is not in fp3 *)
    intro. eapply IN4. eapply get_loc_footprint_incl. eauto.
    auto.
Qed.



(* Some properties of wt_footprint. This lemma says that the
(location, footprint) pairs obtained form disjoint paths are disjoint,
i.e., the locations are disjoint and the footprints have no equal
blocks. To express the disjointness of locaitons, we also need the
type of the footprint to get its size, so we add wt_footprint premises
in this lemma. This lemma is hard to refactor because we do induction
on phl instead of its length. *)
Lemma get_loc_footprint_disjoint_paths: forall phl1 phl2 fp b ofs b1 b2 ofs1 ofs2 fp1 fp2 ty ty1 ty2,
    paths_disjoint phl1 phl2 ->
    list_norepet (footprint_flat fp) ->
    wt_footprint ce ty fp ->
    wt_path ce ty phl1 ty1 ->
    wt_path ce ty phl2 ty2 ->
    get_loc_footprint phl1 fp b ofs = Some (b1, ofs1, fp1) ->
    get_loc_footprint phl2 fp b ofs = Some (b2, ofs2, fp2) ->
    (~ In b (footprint_flat fp)) ->
    (* footprint locations are disjoint *)
    loc_disjoint b1 b2 ty1 ty2 ofs1 ofs2
    (* location and footprint are disjoint *)
    /\ (~ In b1 (footprint_flat fp2))
    /\ (~ In b2 (footprint_flat fp1))
    (* b1 may be equal to b2 so we cannot say b1::fp1 is disjoint with b2::fp2 *)
    /\ list_disjoint (footprint_flat fp1) (footprint_flat fp2).
Proof.
  induction phl1; intros until ty2.
  - intros. inv H.
  - intros DIS NOREP WT WTPH1 WTPH2 G1 G2 IN.
    inv DIS.
    + replace (a::phl1) with ((a::nil) ++ phl1) in WTPH1; auto.
      replace (p2::l2) with ((p2::nil) ++ l2) in WTPH2; auto.
      exploit wt_path_app_inv. eapply WTPH1.
      intros (ty1' & WTPH1' & WTPH1'').
      exploit wt_path_app_inv. eapply WTPH2.
      intros (ty2' & WTPH2' & WTPH2'').
      simpl in G1, G2.
      destruct a; destruct p2; destruct fp; simpl in *; try congruence.
      (* Case1: disjoint struct fields *)
      * destruct (find_fields fid fpl) eqn: FIND1; try congruence. repeat destruct p.
        destruct (find_fields fid0 fpl) eqn: FIND2; try congruence. repeat destruct p.
        exploit find_fields_some; eauto. intros (A1 & A2). subst.
        exploit find_fields_some. eapply FIND1. intros (A3 & A4). subst.
        (* get the subfield types and offsets *)
        inv WT.
        exploit WT2. eapply FIND1. intros (fty1 & FTY1 & FOFS1 & WST1).
        exploit WT2. eapply FIND2. intros (fty2 & FTY2 & FOFS2 & WST2).
        (* tediously get ty1' and ty2' *)
        erewrite <- (app_nil_l [ph_field i]) in WTPH1'.
        eapply wt_path_field_inv in WTPH1' as (id1' & orgs1' & co1' & WTPH1' & CO1' & FTY1' & STR1').
        eapply wt_path_nil_inv in WTPH1'. inv WTPH1'. rewrite CO1' in CO. inv CO.
        rewrite FTY1' in FTY1. inv FTY1.
        erewrite <- (app_nil_l [ph_field i0]) in WTPH2'.
        eapply wt_path_field_inv in WTPH2' as (id2' & orgs2' & co2' & WTPH2' & CO2' & FTY2' & STR2').
        eapply wt_path_nil_inv in WTPH2'. inv WTPH2'. rewrite CO2' in CO1'. inv CO1'.
        rewrite FTY2' in FTY2. inv FTY2.
        (* end of getting ty1' and ty2' *)
        (* field offset no overlap to get loc_disjoint *)
        exploit field_offset_no_overlap_simplified.
        eapply FOFS1. eauto. eapply FOFS2. eauto.
        congruence.
        intros FOFS_DIS.
        assert (LOC_DIS: loc_disjoint b b fty1 fty2 (ofs + z) (ofs + z0)).
        { red. right. lia. }
        (* use get_loc_footprint_disjoint_loc *)        
        exploit get_loc_footprint_disjoint_loc. eapply LOC_DIS. eauto. eauto.
        all: eauto.
        (* prove f and f0 are disjoint using fpl norepet *)
        eapply footprint_norepet_fields_disjoint; eauto.
        congruence.
        (* norepet *)
        (* easy because f and f0 are in fpl and fpl is norepet *)
        eapply footprint_norepet_fields_norepet; eauto.
        eapply footprint_norepet_fields_norepet; eauto.
        intro. eapply IN. eapply in_flat_map. eauto.
        intro. eapply IN. eapply in_flat_map. eauto.
        intro. eapply IN. eapply in_flat_map. eauto.
        intro. eapply IN. eapply in_flat_map. eauto.
      * destruct ty0; try congruence.
        destruct ty3; try congruence.
        repeat destruct ident_eq in *; try congruence;
        repeat destruct list_eq_dec; try congruence. 
    + replace (a::phl1) with ((a::nil)++phl1) in * by auto.
      replace (a::l2) with ((a::nil)++l2) in * by auto.
      exploit wt_path_app_inv. eapply WTPH1.
      intros (ty1' & WTPH1' & WTPH1'').
      exploit wt_path_app_inv. eapply WTPH2.
      intros (ty2' & WTPH2' & WTPH2'').
      exploit get_loc_footprint_app_inv. eapply G1.
      intros (b3 & ofs3 & fp3 & C1 & C2).
      exploit get_loc_footprint_app_inv. eapply G2.
      intros (b4 & ofs4 & fp4 & C3 & C4).
      rewrite C1 in C3. inv C3.
      assert (WTFP4: wt_footprint ce ty1' fp4).
      { exploit get_wt_footprint_wt. eapply WTPH1'. eapply WT.
        eapply get_loc_footprint_eq; eauto.
        eauto. }
      exploit wt_path_det. eapply WTPH1'. eauto. intros. subst.
      (* use I.H. *)
      exploit get_loc_footprint_norepet. eapply NOREP. eauto. eauto.
      intros (D1 & D2).            
      exploit IHphl1; eauto.      
Qed.

End COMP_ENV.

  
(** Initialization of footprint in function entry *)

Definition field_types_to_footprint (ce0: composite_env) (ms: members) (f: type -> footprint): list (ident * Z * footprint) :=
  map (fun '(Member_plain fid fty) =>
         match field_offset ce0 fid ms with
         | OK fofs =>
             (fid, fofs, f fty)
         | Error _ => (* we can prove that it is impossible *)
             (fid, 0, fp_emp)
         end) ms.
    
Section COMP_ENV.

Variable ce0: composite_env.

Section REC.
  
  Variable ce: composite_env.
  Variable rec: forall (ce': composite_env), (removeR ce' ce) -> type -> footprint.

  Definition type_to_empty_footprint' (ty: type) : footprint :=
    match ty with
    | Tstruct _ i =>
        match get_composite ce i with
        | co_some i co P _ =>
            let fields := field_types_to_footprint ce0 (co_members co) (rec (PTree.remove i ce) (PTree_removeR _ _ _ P)) in
            fp_struct i fields
        (* This case is ruled out by syntactic type checking in function entry *)
        | co_none => fp_emp
        end
    | _ => fp_emp
    end.

End REC.

End COMP_ENV.

Definition type_to_empty_footprint ce (ty: type) :=
  Fix (@well_founded_removeR composite) (type_to_empty_footprint' ce) ce ty.


(** well-founded relation of composite env *)

Definition ce_extends (env env': composite_env) : Prop := forall id co, env!id = Some co -> env'!id = Some co.

Lemma ce_extends_remove: forall ce1 ce2 id,
    ce_extends ce1 ce2 ->
    ce_extends (PTree.remove id ce1) ce2.
Proof.
  intros. red.  
  intros. destruct (ident_eq id id0). subst.
  rewrite PTree.grs in H0. inv H0.
  rewrite PTree.gro in H0; eauto.
Qed.

Lemma find_fields_to_footprint: forall ms fid fty fofs f ce
    (FTY: field_type fid ms = OK fty)
    (FOFS: field_offset ce fid ms = OK fofs),
    find_fields fid (field_types_to_footprint ce ms f) = Some (fid, fofs, f fty).
Proof.
  intro ms. unfold field_types_to_footprint, field_offset.
  generalize ms at 2 3.
  generalize 0. 
  induction ms; intros; simpl in *; try congruence.
  destruct a. simpl in *.
  destruct (ident_eq fid id).
  - inv FTY. rewrite FOFS.
    destruct ident_eq; try congruence. auto.    
  - destruct (field_offset_rec ce id ms0 z) eqn:FOFS1;
      destruct ident_eq; try congruence; eauto.
Qed.

Lemma find_fields_to_footprint_inv: forall ms fid fofs f ce ffp
    (FIND: find_fields fid (field_types_to_footprint ce ms f) = Some (fid, fofs, ffp)),
    exists fty, 
      field_type fid ms = OK fty.
Proof.
  intro ms. unfold field_types_to_footprint, field_offset.
  generalize ms at 1.
  generalize 0.
  induction ms; intros; simpl in *; try congruence.
  destruct a. simpl in *.
  destruct (field_offset_rec ce id ms0 z) eqn: FOFS.
  - destruct (ident_eq fid id).
    + inv FIND. eauto.
    + eapply IHms; eauto.
  - destruct (ident_eq fid id).
    + inv FIND. eauto.
    + eapply IHms; eauto.
Qed.

Lemma field_type_member: forall ms fid fty,
    field_type fid ms = OK fty ->
    In (Member_plain fid fty) ms.
Proof.
  induction ms; intros; simpl in *; try congruence.
  destruct a. simpl in *.
  destruct ident_eq.
  inv H. eauto.
  eauto.
Qed.

  
Lemma type_to_empty_footprint_wt_aux: forall ce2 ce1 ty
    (CHECK: check_cyclic_struct ce1 ty = true)
    (EXT: ce_extends ce1 ce2),
    wt_footprint ce2 ty (Fix well_founded_removeR (type_to_empty_footprint' ce2) ce1 ty).
Proof.  
  intros ce2. intros c. pattern c. apply well_founded_ind with (R := removeR).
  eapply well_founded_removeR.
  intros ce1 IH. intros. unfold check_cyclic_struct, type_to_empty_footprint in *.
  erewrite unroll_Fix in *.
  destruct ty; try (simpl; eapply wt_fp_emp; congruence).
  simpl in *. destruct (get_composite ce1 i) eqn: GCO; try congruence. subst.
  eapply andb_true_iff in CHECK as (C1 & C2).
  destruct struct_or_variant_eq in C2; simpl in C2; try congruence.
  eapply wt_fp_struct; eauto.
  - intros fid fty FTY.
    exploit field_type_implies_field_offset; eauto.
    instantiate (1 := ce2).    
    intros (fofs & FOFS).
    exists (Fix well_founded_removeR (type_to_empty_footprint' ce2) (PTree.remove id1 ce1) fty), fofs.    
    repeat apply conj; auto.
    + eapply find_fields_to_footprint; eauto.
    + eapply IH.
      eapply PTree_removeR; eauto.
      erewrite forallb_forall in C1.
      exploit field_type_member. eauto. intros IN.
      generalize (C1 (Member_plain fid fty) IN). auto.
      eapply ce_extends_remove. auto.
  - intros fid fofs ffp FIND.
    exploit find_fields_to_footprint_inv; eauto.
    intros (fty & FTY).
    exploit field_type_implies_field_offset; eauto.
    instantiate (1 := ce2).    
    intros (fofs1 & FOFS).
    exploit find_fields_to_footprint; eauto.
    intros FIND1. erewrite FIND1 in FIND.
    inv FIND.
    exists fty. repeat apply conj; auto.
    eapply IH.
    eapply PTree_removeR; eauto.
    erewrite forallb_forall in C1.
    exploit field_type_member. eauto. intros IN.
    generalize (C1 (Member_plain fid fty) IN). auto.
    eapply ce_extends_remove. auto.
  - unfold name_footprints, field_types_to_footprint, name_members.
    rewrite map_map.
    eapply map_ext_in. intros.
    destruct a. simpl.
    destruct (field_offset ce2 id (co_members co)); auto.
Qed.

Lemma type_to_empty_footprint_wt: forall ce ty
    (CHECK: check_cyclic_struct ce ty = true),
    wt_footprint ce ty (type_to_empty_footprint ce ty).
Proof.   
  intros. eapply type_to_empty_footprint_wt_aux. auto.
  red. auto.
Qed.

Lemma type_to_empty_footprint_flat: forall ce ty,
    footprint_flat (type_to_empty_footprint ce ty) = nil.
Proof.
  intros ce.
  unfold type_to_empty_footprint.
  generalize ce at 1.
  pattern ce. apply well_founded_ind with (R := removeR).
  eapply well_founded_removeR.
  intros ce1 IH. intros. unfold type_to_empty_footprint in *.
  erewrite unroll_Fix in *.
  destruct ty; try (simpl; congruence).
  simpl in *. destruct (get_composite ce1 i) eqn: GCO; try congruence. auto.
  subst. simpl.
  rewrite flat_map_concat_map.
  eapply concat_nil_Forall. 
  eapply Forall_forall. intros.
  eapply in_map_iff in H.
  destruct H as (((id & fofs) & ffp) & A1 & A2). subst.
  eapply in_map_iff in A2.
  destruct A2 as (m & B1 & B2). destruct m.
  destruct (field_offset ce0 id0 (co_members co)) eqn: FOFS; inv B1; auto.
  eapply IH. eapply PTree_removeR. eauto.
Qed.  

(** Initialization of footprint map in function entry *)

(* We should consider Tstruct ! *)
Fixpoint init_footprint_map ce (l: list (ident * type)) (fpm: fp_map) :=
  match l with
  | nil => fpm
  | (id, ty) :: l' =>
      init_footprint_map ce l' (PTree.set id (type_to_empty_footprint ce ty) fpm)
  end.


Lemma init_footprint_map_app: forall l1 l2 fpm ce,
    init_footprint_map ce (l1 ++ l2) fpm =
      init_footprint_map ce l2 (init_footprint_map ce l1 fpm).
Proof.
  induction l1; simpl; eauto; intros.
  destruct a.  erewrite IHl1; eauto.
Qed.

Lemma init_footprint_map_get_inv: forall l fpm id fp ce,
    (init_footprint_map ce l fpm) ! id = Some fp ->
    (exists ty, In (id, ty) l /\ fp = type_to_empty_footprint ce ty)
    \/ fpm ! id = Some fp.
Proof.
  induction l; intros; simpl in *.
  - eauto.
  - destruct a.
    exploit IHl; eauto. intros [(ty & A1 & A2) | A2].
    + subst. left. exists ty. eauto.
    + rewrite PTree.gsspec in A2.
      destruct peq.
      * subst. inv A2. left. exists t. eauto.
      * eauto.
Qed.

Lemma init_footprint_map_get_not_in: forall l fpm id ce,
    ~ In id (var_names l) ->
    (init_footprint_map ce l fpm) ! id = fpm ! id.
Proof.
  induction l; simpl; auto; intros.
  destruct a. simpl in *.
  eapply Decidable.not_or in H. destruct H.
  erewrite IHl; eauto.
  rewrite PTree.gso; auto.
Qed.  
  
Lemma init_footprint_map_flat_element: forall l fpm id ty ce
    (IN: In (id, ty) l),
    exists fp, (init_footprint_map ce l fpm) ! id = Some fp
          /\ footprint_flat fp = nil.
Proof.
  intro. cut (exists n, length l = n); eauto. intros (n & LEN).
  generalize dependent l.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst. simpl in *.
    contradiction.
  - eapply length_S_inv in LEN. destruct LEN as (l' & (id1 & ty1) & APP & LEN).
    subst.
    eapply in_app in IN. destruct IN.
    + exploit IHn; eauto. instantiate (1 := fpm).
      intros (fp & A1 & A2).
      erewrite init_footprint_map_app. simpl.
      rewrite PTree.gsspec.
      destruct peq; subst.
      * eexists. split; eauto.
        eapply type_to_empty_footprint_flat.
      * rewrite A1. eauto.
    + inv H; try contradiction.
      inv H0.
      erewrite init_footprint_map_app. simpl.
      rewrite PTree.gss.
      eexists. split; eauto.
      eapply type_to_empty_footprint_flat.
Qed.

Lemma init_footprint_map_flat: forall l fpm1 ce
    (NIN: forall id ty, In (id, ty) l -> fpm1 ! id = None),
    (* (NOREP: list_norepet (var_names l)), *)
    list_equiv (flat_fp_map (init_footprint_map ce l fpm1)) (flat_fp_map fpm1).
Proof.
  induction l; simpl; intros; auto.
  red. intros. split; auto.
  destruct a.
  red. intros. split.
  - intros.
    destruct (in_dec ident_eq p (var_names l)).
    (* show that IN2 is impossible because fp is empty *)
    + eapply in_flat_map in H.
      destruct H as ((id & fp) & IN1 & IN2).
      eapply PTree.elements_complete in IN1.
      exploit init_footprint_map_get_inv; eauto.
      intros [(ty & A1 & A2) | A2].
      * subst. simpl in IN2. rewrite type_to_empty_footprint_flat in IN2.
        inv IN2.
      * rewrite PTree.gsspec in A2.
        destruct peq; auto.
        inv A2. simpl in IN2. rewrite type_to_empty_footprint_flat in IN2.
        inv IN2.
        eapply in_flat_map; eauto.
        exists (id, fp). simpl. split; auto.
        eapply PTree.elements_correct. auto.
    + exploit (IHl (PTree.set p (type_to_empty_footprint ce t) fpm1)).
      simpl. intros. rewrite PTree.gsspec.
      destruct peq; subst.
      exfalso. eapply n. eapply in_map_iff. exists (p, ty). eauto.
      eapply NIN; eauto.
      instantiate (1 := x). intros EQUIV2.
      erewrite EQUIV2 in H.
      eapply in_flat_map in H.
      destruct H as ((id & fp) & IN1 & IN2).
      eapply PTree.elements_complete in IN1. erewrite PTree.gsspec in IN1.
      destruct (peq id p); subst.
      * inv IN1.  simpl in IN2.
        erewrite type_to_empty_footprint_flat in IN2. inv IN2.
      * eapply in_flat_map.
        exists (id, fp). split. eapply PTree.elements_correct. eauto. auto.
  - intros IN. eapply in_flat_map in IN.
    destruct IN as ((id & fp) & IN1 & IN2).
    eapply PTree.elements_complete in IN1.
    destruct (in_dec ident_eq id (var_names l)).
    + eapply in_map_iff in i. destruct i as ((id1 & ty) & B1 & B2).
      simpl in B1. subst.
      exploit NIN. right. eauto. intros C1. rewrite IN1 in C1. inv C1.
    + eapply in_flat_map.
      exists (id, fp). split; auto.
      eapply PTree.elements_correct.
      erewrite init_footprint_map_get_not_in; eauto.
      rewrite PTree.gsspec.
      destruct peq.
      * subst. exploit NIN; eauto. intros. rewrite IN1 in H. inv H.
      * auto.
Qed.

