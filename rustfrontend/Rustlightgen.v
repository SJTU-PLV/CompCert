Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Rusttypes.
Require Import Cop.
Require Import Rustsyntax Rustlight.
Require Import Errors.

Import ListNotations.
(** * Rustsyntax to Rustlight *)

Parameter dummy_origin : unit -> origin.

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  (* gen_next: ident; *)
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), (* Ple (gen_next g) (gen_next g') -> *) result A g.


Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (* (Ple_refl (gen_next g)) *).

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

Declare Scope gensym_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : gensym_monad_scope.

Section SIMPL_EXPR.

Variable ce: composite_env.
  
Local Open Scope gensym_monad_scope.


Parameter fresh_atom : unit -> ident.

Definition initial_generator : generator :=
  mkgenerator nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) =>
    let fresh_id := (fresh_atom Datatypes.tt) in
    Res fresh_id
      (mkgenerator ((fresh_id, ty) :: gen_trail g)).

(** Use mode of an l-value  *)

Inductive use_mode : Type :=
| Use_copy: use_mode         (**r copy the l-value to other place *)
| Use_deref: use_mode          (**r use the l-value to perform dereference *)
| Use_reference: use_mode.     (**r just use the address of this l-value *)


(** TODO: for_set is useful in reducing the number of temporary
variables, because in most of the time we create a temp var to store
the result of the value expression and return Eplace/Emoveplace. But
with for_set, we can just use the set destination to store the result
of the value expression *)
Inductive destination : Type :=
| For_val
| For_effects
| For_set (p: place).

Definition finish (dst: destination) (sl: list statement) (a: expr) :=
  match dst with
  | For_val => (sl, a)
  | For_effects => (sl, a)
  | For_set sd => (sl ++ (Sassign sd a :: nil), a)
  end.

Let type_eq := type_eq_except_origins.

(* generate assign fields statement lists *)
Fixpoint fields_assign (p: place) (ids : list ident) (args: list expr) (membs: members) {struct ids}: mon (list statement) :=
  match ids, args, membs with
  | nil, nil, nil => ret nil
  | id :: ids', arg :: args', (Member_plain fid fty) :: membs' =>
      if ident_eq id fid then
        if type_eq (typeof arg) fty then
          do stmts <- fields_assign p ids' args' membs';
          ret (Sassign (Pfield p fid fty) arg :: stmts)
        else
          error [CTX (local_of_place p); CTX id; CTX fid; MSG ": have different type in fields_assign"]
      else
        error [CTX (local_of_place p); CTX id; CTX fid; MSG ": have different ident in fields_assign"]
  | _, _ , _ =>
      error [CTX (local_of_place p); MSG ": inconsistent number of fields ident, arg idents and members in fields_assign"]
  end.

Definition dummy_expr := Econst_int Int.zero type_int32s.

(** ** Translate expression  *)


Section NOTATION.
(* Some ad-hoc solution to utilize the coercion from pexpr(place) to expr *)
Local Notation "( x , y )" := (@pair (list statement) expr x y).
Local Notation "( x ,, y )" := (@pair (list statement) place x y).

Fixpoint transl_value_expr (e: Rustsyntax.expr) : mon (list statement * expr) :=
  match e with
  | Rustsyntax.Eunit => ret (nil, Eunit)
  | Rustsyntax.Eval (Vint n) ty =>
      ret (nil, Econst_int n ty)
  | Rustsyntax.Eval (Vfloat n) ty =>
      ret (nil, Econst_float n ty)
  | Rustsyntax.Eval (Vsingle n) ty =>
      ret (nil, Econst_single n ty)
  | Rustsyntax.Eval (Vlong n) ty =>
      ret (nil, Econst_long n ty)
  | Rustsyntax.Eval _ ty =>
      error (msg "Rustlightgen.transl_expr: Eval")
  | Rustsyntax.Eglobal id ty =>
      ret (nil, Eglobal id ty)
  | Rustsyntax.Estruct id fids args ty =>
      (* let temp : ty in
         temp.fid1 := arg1;
         temp.fid2 := agr2;
         ... *)
      match ty with
      | Tstruct _ struct_id =>
          if ident_eq struct_id id then
            (* evaluate the structure arguments *)
            match ce!id with
            | Some co =>
                (**TODO: we can optimize the generated code by eliminating the generated temp variable to reduce the overhead of memory copying *)
                do temp_id <- gensym ty;
                let temp := Plocal temp_id ty in
                do (args_stmts, args_exprs) <- transl_exprlist args;
                do fields_assign_stmts <- fields_assign temp fids args_exprs co.(co_members);
                let ret_expr := if own_type ce ty then Emoveplace temp ty else Eplace temp ty in
                ret (args_stmts ++ fields_assign_stmts, ret_expr)
            | _ =>
                error [CTX id; MSG ": there is no composite for it (triggered in transl_value_expr) "]
            end
          else error [CTX id; CTX struct_id; MSG ": structure construction has inconsistent structure identifiers in transl_value_expr"]
      | _ =>
          error [CTX id; MSG ": structure construction type error in transl_value_expr"]
      end
  | Eenum id fid e ty =>
      match ty with
      | Tvariant _ variant_id =>
          (* a simple type checking *)
          if ident_eq variant_id id then
            match ce!id with
            | Some co =>
                do (stmt, rhs) <- transl_value_expr e;
                do temp_id <- gensym ty;
                let temp := Plocal temp_id ty in
                let ret_expr := if own_type ce ty then Emoveplace temp ty else Eplace temp ty in
                ret (stmt ++ [Sassign_variant temp id fid rhs], ret_expr)
            | _ =>
                error [CTX id; MSG ": there is no composite for it in transl_value_expr"]
            end
          else
            error [CTX id; CTX variant_id; MSG ": variant construction has inconsistent structure identifiers in transl_value_expr"]
      | _ => error [CTX id; MSG ": variant construction type error in transl_value_expr"]
      end
  | Rustsyntax.Evar id ty =>
      (* use id as value *)
      let p := Plocal id ty in
      (* check if ty is a copy type *)
      if own_type ce ty then
        ret (nil, Emoveplace p ty)
      else
        ret (nil, Eplace p ty)
  | Ederef e ty =>
      (* consider *call_allocate_box() *)
      do (sl, p) <- transl_place_expr e;
      let p' := Pderef p ty in
      if own_type ce ty then
        ret (sl, Emoveplace p' ty)
      else
        ret (sl, Eplace p' ty)
  | Ebox e ty =>
      do (sl, e') <- transl_value_expr e;
      (* Introduce a new variable. The scope of this new variable is
      the statement. *)
      do temp_id <- gensym ty;
      let temp := Plocal temp_id ty in
      let box_stmt := Sbox temp e' in
      ret (sl ++ (box_stmt :: nil), Emoveplace temp ty)
  | Rustsyntax.Eref org mut e ty =>
      do (sl, p) <- transl_place_expr e;
      ret (sl, Eref org mut p ty)
  | Efield e fid ty =>
      do (sl, p) <- transl_place_expr e;
      let p' := Pfield p fid ty in
      if own_type ce ty then
        ret (sl, Emoveplace p' ty)
      else
        ret (sl, Eplace p' ty)
  | Eassign l r ty =>
      let ty1 := Rustsyntax.typeof l in
      let ty2 := Rustsyntax.typeof r in
      (* simple type checking *)
      if type_eq ty1 ty2 then        
        do (sl1, p) <- transl_place_expr l;
        do (sl2, e') <- transl_value_expr r;
        let s := Sassign p e' in
        ret (sl2 ++ sl1 ++ (s :: nil), dummy_expr)
      else
        error (msg "Type mismatch between LHS and RHS in assignment: transl_expr")
        (* The following code is about the assignment of variant based on type *)
        (* match ty1 with *)
        (* (* assign value to a variant *) *)
        (* | Tvariant id _ => *)
        (*     match ce!id with *)
        (*     | Some co => *)
        (*         if in_dec type_eq ty2 (map type_member co.(co_members)) then *)
        (*           do (sl1, p) <- transl_place_expr l; *)
        (*           do (sl2, e') <- transl_value_expr r; *)
        (*           let s := Sassign p e' in *)
        (*           ret (sl2 ++ sl1 ++ (s :: nil), dummy_expr) *)
        (*         else *)
        (*           error (msg "In assignment, LHS has type variant but the type of RHS is no in the fields of this variant") *)
        (*     | _ => error (msg "In assignment, LHS has type variant but does not exist in the composite environment") *)
        (*     end *)
        (* | _ => error (msg "Type mismatch between LHS and RHS in assignment: transl_expr") *)
        (* end *)
  | Ecall e el ty =>
      do (sl1, ef') <- transl_value_expr e;
      do (sl2, el') <- transl_exprlist el;
      (* use a temp to store the result of this call *)
      do temp_id <- gensym ty;
      let temp := Plocal temp_id ty in
      let call_stmt := Scall temp ef' el' in
      if own_type ce ty then
        (* if this call is used for effects, the returned expr is useless *)
        ret (sl1 ++ sl2 ++ (call_stmt :: nil), Emoveplace temp ty)
      else
        ret (sl1 ++ sl2 ++ (call_stmt :: nil), Eplace temp ty)
  | Rustsyntax.Eunop uop e ty =>
      do (sl, e') <- transl_value_expr e;
      match e' with
      | Epure pe' =>
          ret (sl, Eunop uop pe' ty)
      | _ =>
          error (msg "Move in unop: Rustlightgen.transl_expr")
      end
  | Rustsyntax.Ebinop binop e1 e2 ty =>
      do (sl1, e1') <- transl_value_expr e1;
      do (sl2, e2') <- transl_value_expr e2;
      match e1', e2' with
      | Epure pe1', Epure pe2' =>          
          ret (sl1 ++ sl2, Ebinop binop pe1' pe2' ty)
      | _, _ =>
          error (msg "Move in binop: Rustlightgen.transl_expr")
      end      
 end
  
with transl_place_expr (e: Rustsyntax.expr) : mon (list statement * place) :=
  match e with
  | Rustsyntax.Evar id ty =>
      ret (nil,, Plocal id ty)
  | Rustsyntax.Ederef e ty =>
      do (sl, p) <- transl_place_expr e;
      ret (sl,, Pderef p ty)
  | Rustsyntax.Ebox e ty =>
      (* temp = Box(e);
         Plocal temp *)
      do (sl, e') <- transl_value_expr e;
      do temp_id <- gensym ty; (* what is the lifetime of temp? *)
      let temp := Plocal temp_id ty in
      let box_stmt := Sbox temp e' in
      ret (sl ++ (box_stmt :: nil),, temp)
  | Efield e fid ty =>
      do (sl, p) <- transl_place_expr e;
      ret (sl,, Pfield p fid ty)
  | Ecall ef el ty =>
      do (sl1, ef') <- transl_value_expr ef;
      do (sl2, el') <- transl_exprlist el;
      (* use a temp to store the result of this call *)
       do temp_id <- gensym ty;
      let temp := Plocal temp_id ty in
      let call_stmt := Scall temp ef' el' in
      ret (sl1 ++ sl2,, temp)
  | _ => error (msg "It is impossible that this expression is a place expression: Rustlightgen.transl_expr")
  end
    
    
with transl_exprlist (el: Rustsyntax.exprlist) : mon (list statement * list expr) :=
       match el with
       | Rustsyntax.Enil =>
           ret (pair nil nil)
       | Rustsyntax.Econs r1 rl2 =>
           do (sl1, a1) <- transl_value_expr r1;
           do (sl2, al2) <- transl_exprlist rl2;
           ret (pair (sl1 ++ sl2) (a1 :: al2))
       end.

End NOTATION.


(* Replace binder with a place in Rustlight expression and statements *)

Fixpoint replace_binder_in_place (id: ident) (p1: place) (p2: place) : place :=
  match p2 with
  | Plocal id' _ =>
      if ident_eq id id' then p1 else p2
  | Pderef p' ty =>
      Pderef (replace_binder_in_place id p1 p') ty
  | Pfield p' fid ty =>
      Pfield (replace_binder_in_place id p1 p') fid ty
  | Pdowncast p' fid ty =>
      Pdowncast (replace_binder_in_place id p1 p') fid ty
  end.

Fixpoint replace_binder_in_pexpr (id: ident) (p: place) (e: pexpr) : pexpr :=
  match e with
  | Eplace p' ty =>
      Eplace (replace_binder_in_place id p p') ty
  | Eref org mut p' ty =>
      Eref org mut (replace_binder_in_place id p p') ty
  | Ecktag p' fid =>
      Ecktag (replace_binder_in_place id p p') fid
  | Eunop unop pe ty =>
      Eunop unop (replace_binder_in_pexpr id p pe) ty
  | Ebinop bop e1 e2 ty =>
      Ebinop bop (replace_binder_in_pexpr id p e1) (replace_binder_in_pexpr id p e2) ty
  | _ => e
  end.

Definition replace_binder_in_expr (id: ident) (p: place) (e: expr) : expr :=
  match e with
  | Emoveplace p' ty =>
      Emoveplace (replace_binder_in_place id p p') ty
  | Epure pe =>
      replace_binder_in_pexpr id p pe
  end.

Fixpoint replace_binder_in_stmt (id: ident) (p: place) (s: statement) : statement :=
  match s with
  | Slet id' ty s' => Slet id' ty (replace_binder_in_stmt id p s')
  | Sassign p' e =>
      Sassign (replace_binder_in_place id p p') (replace_binder_in_expr id p e)
  | Sassign_variant p' enum_id fid e =>
      Sassign_variant (replace_binder_in_place id p p') enum_id fid (replace_binder_in_expr id p e)
  | Sbox p' e =>
      Sbox (replace_binder_in_place id p p') (replace_binder_in_expr id p e)
  | Scall p' ef al =>
      Scall (replace_binder_in_place id p p') (replace_binder_in_expr id p ef) (map (replace_binder_in_expr id p) al)
  | Ssequence s1 s2 =>
      Ssequence (replace_binder_in_stmt id p s1) (replace_binder_in_stmt id p s2)
  | Sifthenelse e s1 s2 =>
      Sifthenelse e (replace_binder_in_stmt id p s1) (replace_binder_in_stmt id p s2)
  | Sloop s =>
      Sloop (replace_binder_in_stmt id p s)
  | Sreturn p =>
      Sreturn (replace_binder_in_place id p p)
  | _ => s
  end.
         

Definition value_or_place (e: Rustsyntax.expr) : bool :=
  match e with
  | Rustsyntax.Eunit => true
  | Rustsyntax.Estruct _ _ _ _ => true
  | Rustsyntax.Eenum _ _ _ _ => true
  | Rustsyntax.Eval _ _ => true
  | Rustsyntax.Evar _ _ => false
  | Rustsyntax.Ebox _ _ => true
  | Rustsyntax.Eref _ _ _ _ => true
  | Rustsyntax.Efield _ _ _ => false
  | Rustsyntax.Ederef _ _ => false
  | Rustsyntax.Eunop _ _ _ => true
  | Rustsyntax.Ebinop _ _ _ _ => true
  | Rustsyntax.Eassign _ _ _ => true
  | Rustsyntax.Ecall _ _ _ => true
  | Rustsyntax.Eglobal _ _ => true
  end.
           
Fixpoint generate_lets (l: list (ident * type)) (body: statement) : statement :=
  match l with
  | nil => body
  | (id, ty) :: l' =>
      Slet id ty (generate_lets l' body)
  end.

Fixpoint makeseq_rec (s: statement) (l: list statement) : statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq_rec (Ssequence s s') l'
  end.

Definition makeseq (l: list statement) : statement :=
  makeseq_rec Sskip l.

Definition finish_stmt (sl: list statement) : mon statement :=
  fun (g: generator) =>
    let s := makeseq sl in
    Res (generate_lets (gen_trail g) s)
      (mkgenerator nil).

Definition extract_temps : mon (list (ident * type)) :=
  fun (g: generator) =>
    Res (gen_trail g)
      (mkgenerator nil).


(** Smart constructor for [if ... then ... else]. (copy from SimplExpr.v) *)


(** TODO: some optimizations  *)
Definition makeif (a: expr) (s1 s2: statement) : statement :=
  (* match eval_simpl_expr a with *)
  (* | Some v => *)
  (*     match bool_val v (typeof a) Mem.empty with *)
  (*     | Some b => if b then s1 else s2 *)
  (*     | None   => Sifthenelse a s1 s2 *)
  (*     end *)
  (* | None => *) Sifthenelse a s1 s2.


Definition transl_if (r: Rustsyntax.expr) (s1 s2: statement) : mon statement :=
  do (sl, a) <- transl_value_expr r;
  (**TODO: check the usage of finish_stmt *)
  do s <- finish_stmt sl;
  ret (Ssequence s (makeif a s1 s2)).

(* the returned gen_trail must be empty to ensure that all the new
introduced variables are declared by let statements *)
Fixpoint transl_stmt (stmt: Rustsyntax.statement) : mon statement :=
  match stmt with
  | Rustsyntax.Sskip =>
      ret Sskip
  | Sdo e =>
      do (sl, _) <- transl_value_expr e;
      (* insert let statements *)
      finish_stmt sl
  | Rustsyntax.Slet id ty None stmt' =>
      do s <- transl_stmt stmt';
      ret (Slet id ty s)
  | Rustsyntax.Slet id ty (Some e) stmt' =>
      let rhs_ty := Rustsyntax.typeof e in
      (* simple type checking *)
      if type_eq ty rhs_ty then        
        do (sl1, e') <- transl_value_expr e;
        let s := Sassign (Plocal id ty) e' in
        (* Important: the lifetime of the temporary variable generated in [e] must exceed the assignment [s] *)
        do sl1' <- finish_stmt (sl1 ++ [s]);
        do sl2 <- transl_stmt stmt';        
        ret (Slet id ty (Ssequence sl1' sl2))
      else
        error [CTX id; MSG ": Type mismatch between LHS and RHS in let initialization: transl_stmt"]
  | Rustsyntax.Ssequence s1 s2 =>
      do s1' <- transl_stmt s1;
      do s2' <- transl_stmt s2;
      ret (Ssequence s1' s2')
  | Rustsyntax.Sifthenelse e s1 s2 =>
      (* TODO: To ensure safety or no leak? e' must not be move expression *)
      do (sl, e') <- transl_value_expr e;
      (* e is in temporary scope *)
      do s' <- finish_stmt sl;
      do s1' <- transl_stmt s1;
      do s2' <- transl_stmt s2;
      ret (Ssequence s' (Sifthenelse e' s1' s2'))
  | Swhile e body =>
      do cond <- transl_if e Sskip Sbreak;
      do body' <- transl_stmt body;
      ret (Sloop (Ssequence cond body'))
  | Rustsyntax.Sloop s =>
      do s' <- transl_stmt s;
      ret (Sloop s')
  | Rustsyntax.Sreturn e =>
      do (sl, p) <- transl_place_expr e;
      (* The lifetime of the temporary variable must exceed the return statement *)
      do s' <- finish_stmt (sl ++ [Sreturn p]);
      ret s'
  | Rustsyntax.Sbreak =>
      ret Sbreak
  | Rustsyntax.Scontinue =>
      ret Scontinue
  | Rustsyntax.Smatch e arm_body =>
      (** FIXME: too complicated  *)
      (* we want to store e into a place *)
      let ty := Rustsyntax.typeof e in
      match ty with
      | Tvariant _ id =>
          match ce!id with
          | Some co =>
              if value_or_place e then
                (* let .. (generate_lets)
                   cond_sl; (eval_cond)
                   let temp;                  -| 
                   temp = e'; (assign_temp)    |-> temp_decl_arm
                   if cktag(temp,fid1) ...    _|  *)
                do temp_id <- gensym ty;
                let temp := Plocal temp_id ty in
                do (cond_sl, e') <- transl_value_expr e;
                let eval_cond := makeseq cond_sl in
                let assign_temp := Sassign temp e' in
                (* temps are the generated variable in match scrutinee
                whose scope contains the entire match *)
                do temps <- extract_temps;
                do arm_stmt <- transl_arm_statements arm_body temp co;
                (* concat the condition statements and generate let stmts *)
                let temp_decl_arm := Slet temp_id ty (Ssequence assign_temp arm_stmt) in
                ret (generate_lets temps temp_decl_arm)
              else
                do (cond_sl, p) <- transl_place_expr e;
                let eval_cond := makeseq cond_sl in
                do temps <- extract_temps;
                do arm_stmt <- transl_arm_statements arm_body p  co;
                ret (generate_lets temps (Ssequence eval_cond arm_stmt))                
          | None => error (msg "Variant type does not exist: Rustlightgen.simpl_stmt")
          end
      | _ => error (msg "Type error in match: Rustlightgen.simpl_stmt")
      end        
  end

(** TODO: support match a reference of a enum  *)
with transl_arm_statements (sl: arm_statements) (p: place) (co: composite) : mon statement :=
  match sl with
  | ASnil => ret Sskip      
  | AScons ids arm sl' =>
      do arm' <- transl_stmt arm;
      match ids with
      | Some (fid, temp_id) =>
          (* Replace temp_id with (p as fid) in [arm] *)
          match List.find (fun elt => ident_eq (name_member elt) fid) co.(co_members) with
          | Some m =>
              let ty := type_member m in
              (* replace generic origins in ty with dummy origins *)
              let dummy_org := dummy_origin Datatypes.tt in
              let ty := replace_type_with_dummy_origin dummy_org ty in
              let cond := Ecktag p fid in
              let p' := Pdowncast p fid ty in
              (* move p' or copy p'. TODO: support [&mut] p' *)
              let then_stmt := replace_binder_in_stmt temp_id p' arm' in
              (* (** FIXME: We do not want to (p as fid) *) *)
              (* let destruct_place := if moved then Emoveplace p' ty else (Epure (Eplace p' ty)) in *)
              (* let assign_temp := Sassign (Plocal temp_id ty) destruct_place in *)
              (* let then_stmt := Slet temp_id ty (Ssequence assign_temp arm') in *)
              match sl' with
              | ASnil =>
                  (* Some optimization: the last branch, no need to check the tag*)
                  ret then_stmt
              | AScons _ _ _ =>
              (* if cond then
                   then_stmt
                else else_stmt *)              
                  do else_stmt <- transl_arm_statements sl' p co;
                  ret (Sifthenelse cond then_stmt else_stmt)
              end
          | _ => error (msg "Cannot find the member: Rustlightgen.transl_arm_statements")
          end
      | None =>
          (* default arm: else_stmt is useless *)
          ret arm'
      end
  end.

(* Extract the let declared variables in Rustsyntax, which are used to
generate fresh variables *)
Fixpoint extract_vars (stmt: Rustsyntax.statement) : list (ident * type) :=
  match stmt with
  | Rustsyntax.Slet id ty _ s =>
      (id,ty) :: extract_vars s
  | Rustsyntax.Ssequence s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Rustsyntax.Sifthenelse _ s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | Rustsyntax.Sloop s =>
      extract_vars s
  | Rustsyntax.Swhile _ s =>
      extract_vars s
  | _ => nil
  end.

(* Extract the let declared variables which are used to construct the
variables list. *)
Fixpoint extract_rustlight_vars (stmt: statement) : list (ident * type) :=
  match stmt with
  | Slet id ty s =>
      (id,ty) :: extract_rustlight_vars s
  | Ssequence s1 s2 =>
      extract_rustlight_vars s1 ++ extract_rustlight_vars s2
  | Sifthenelse _ s1 s2 =>
      extract_rustlight_vars s1 ++ extract_rustlight_vars s2
  | Sloop s =>
      extract_rustlight_vars s
  | _ => nil
  end.


Open Scope error_monad_scope.

Definition transl_function (f: Rustsyntax.function) : Errors.res function :=
  let vars := var_names (f.(Rustsyntax.fn_params) ++ (extract_vars f.(Rustsyntax.fn_body))) in
  let next_temp := Pos.succ (fold_left (fun acc elt => Pos.max acc elt) vars 1%positive) in
  match transl_stmt f.(Rustsyntax.fn_body) initial_generator with
  | Res stmt g =>
      (** IMPORTANT: collect the declared variables here, before this
      pass, function does not contain the variable list. We collect
      them in this pass because after this pass, the declared variable
      would not be changed a lot. *)
      let vars := extract_rustlight_vars stmt in
      if in_dec ident_eq (fst f.(Rustsyntax.fn_return)) (var_names vars) then
        Errors.Error (msg "The return variable is declared in the function (Rustlightgen) ")
      else
      Errors.OK (mkfunction f.(Rustsyntax.fn_generic_origins)
                            f.(Rustsyntax.fn_origins_relation)
                            f.(Rustsyntax.fn_drop_glue)
                            (snd f.(Rustsyntax.fn_return))
                            f.(Rustsyntax.fn_callconv)
                            (** Note that we should add the return
                            variable to the variables list *)
                            (f.(Rustsyntax.fn_return) :: vars)
                            f.(Rustsyntax.fn_params)
                            stmt)
  | Err msg => Errors.Error msg
  end.

Definition transl_fundef (fd: Rustsyntax.fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      do tf <- transl_function f;
      Errors.OK (Internal tf)
  | External orgs org_rels ef targs tres cconv =>
      Errors.OK (External orgs org_rels ef targs tres cconv)
  end.

End SIMPL_EXPR.

Open Scope error_monad_scope.

Definition transl_program (p: Rustsyntax.program) : Errors.res program :=
  do p1 <- transform_partial_program (transl_fundef p.(prog_comp_env)) p;
  Errors.OK
    {| prog_defs := p1.(AST.prog_defs);
    prog_public := p1.(AST.prog_public);
    prog_main := p1.(AST.prog_main);
    prog_types := p.(prog_types);  
    prog_comp_env := p.(prog_comp_env);
    prog_comp_env_eq := p.(prog_comp_env_eq) |}.
