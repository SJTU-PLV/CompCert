Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rustlight.

Local Open Scope error_monad_scope.
Import ListNotations.

(** A Linked list implemented in Rustlight *)

(* Declaration of the ident of variables *)

Definition Node : ident := 132%positive.
Definition node : ident := 164%positive.
Definition key : ident := 121%positive.
Definition val : ident := 52%positive.
Definition next : ident := 80%positive.
Definition List : ident := 141%positive.
Definition Nil : ident := 61%positive.
Definition Cons : ident := 149%positive.
Definition find : ident := 87%positive.
Definition l : ident := 110%positive.
Definition k : ident := 109%positive.
Definition _retv : ident := 13%positive.
Definition process : ident := 122%positive.
Definition empty_list : ident := 142%positive.
Definition insert : ident := 127%positive.
Definition v : ident := 120%positive.
Definition head : ident := 9%positive.
Definition remove : ident := 74%positive.
Definition delete_list : ident := 29%positive.
Definition __drop_in_place_Node : ident := 89%positive.
Definition __drop_in_place_List : ident := 16%positive.
Definition malloc : ident := 191%positive.
Definition free : ident := 17%positive.
Definition hash : ident := 32%positive.
Definition range : ident := 15%positive.
Definition tmp : ident := 12%positive.
Definition tmpv : ident := 177%positive.
(* Definition _32 : ident := 177%positive. *)
Definition _33 : ident := 143%positive.
Definition _34 : ident := 111%positive.
Definition _35 : ident := 75%positive.
Definition _36 : ident := 41%positive.
Definition _37 : ident := 7%positive.
Definition _38 : ident := 172%positive.
Definition _39 : ident := 138%positive.
Definition _40 : ident := 77%positive.
Definition _41 : ident := 43%positive.
Definition _42 : ident := 10%positive.
Definition _43 : ident := 174%positive.
Definition wildcard : ident := 106%positive.

(* type declaration *)
Definition List_ty : type := Tvariant nil List.
Definition Node_ty : type := Tstruct nil Node.

Definition type_int32u := Tint I32 Unsigned.

(* function types declaration *)
Definition process_ty : type := Tfunction nil nil (Tcons (Tbox type_int32s) Tnil) (Tbox type_int32s) cc_default.

Local Open Scope rustlight_scope.

(* hash function *)

Definition hash_body : statement :=
  <{ _retv#type_int32u := copy k#type_int32s % copy range#type_int32u;
     return (_retv#type_int32u) }>.

Definition hash_func : function :=
  {| fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := None;
    fn_return := type_int32u;
    fn_callconv := cc_default;
    fn_vars := [(_retv, type_int32u)];
    fn_params := [(k, type_int32s); (range, type_int32u)];
    fn_body := hash_body |}.

(* find_function *)

Definition List_box : type := Tbox List_ty.
Definition find_ty : type := Tfunction nil nil (Tcons List_box (Tcons type_int32s Tnil)) List_box cc_default.
Definition Tbox_int : type := Tbox type_int32s.

(* argument: l: List_box and k: type_int32s *)
Definition find_body : statement :=
  <{ if (cktag (! (l#List_box)) is Nil) then
       (* let wildcard : Tunit in *)
       (*   wildcard#Tunit := copy (!l#List_box) as Nil <Tunit>; *)
       (*   _retv#List_box := move l#List_box; *)
       (* return _retv#List_box *)
       _retv#List_box := move l#List_box;
       return _retv#List_box
       (* end *)
     else
       let node : Node_ty in
         node#Node_ty := move (!l#List_box) as Cons <Node_ty>;
         if (copy k#type_int32s == copy node#Node_ty proj key<type_int32s>) then
           (* let _31 : type_int32s in *)
           (*   _31#type_int32s <- process<process_ty> @ {pure (copy k#type_int32s), pure (copy node#Node_ty proj val <type_int32s>)}; *)
           (*   node#Node_ty proj val <type_int32s> := copy _31#type_int32s *)
           (* end; *)
           (* let _32 : List_ty in *)
           (*   _32#List_ty :=v List::Cons(move node#Node_ty);  *)
           (*   (!l#List_box) := move _32#List_ty *)
           (* end; *)
           (* _retv#List_box := move l#List_box; *)
           (* return _retv#List_box *)
           let tmpv : Tbox_int in
             tmpv#Tbox_int <- process<process_ty> @ {move node#Node_ty proj val <Tbox_int>};
             node#Node_ty proj val <Tbox_int> := move tmpv#Tbox_int
           end
         else
           (* let _33 : List_box in *)
           (*   _33#List_box <- find<find_ty> @ {move node#Node_ty proj next<List_box>, pure (copy k#type_int32s)}; *)
           (*   node#Node_ty proj next<List_box> := move _33#List_box *)
           (* end; *)
           (* let _34 : List_ty in *)
           (*   _34#List_ty :=v List::Cons(move node#Node_ty);  *)
           (*   (!l#List_box) := move _34#List_ty *)
           (* end; *)
           (* _retv#List_box := move l#List_box; *)
           (* return _retv#List_box *)
           (** We do not support node.next = process(move node.next,
           k) for now *)
           let tmp : List_box in
             tmp#List_box <- find<find_ty> @ {move node#Node_ty proj next<List_box>, pure (copy k#type_int32s)};
             node#Node_ty proj next<List_box> := move tmp#List_box
           end
         fi;
         (!l#List_box) :=v List::Cons(move node#Node_ty);
         _retv#List_box := move l#List_box;
         return _retv#List_box
      end
      fi }>.
 
Definition find_func : function :=
  {| fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := None;
    fn_return := List_box;
    fn_callconv := cc_default;
    (* fn_vars := [(_retv, List_box); (wildcard, Tunit); (node, Node_ty); (_31, type_int32s); (_32, List_ty); (_33, List_box); (_34, List_ty)]; *)
    fn_vars := [(_retv, List_box); (node, Node_ty); (tmp, List_box); (tmpv, Tbox_int)];
    fn_params := [(l, List_box); (k, type_int32s)];
    fn_body := find_body |}.
  

(* empty_list function *)

Definition empty_list_body : statement :=
  <{ let _36: List_box in
     let _35: List_ty in
     _35#List_ty :=v List::Nil(Ett);
     _36#List_box :=b move _35#List_ty;
     _retv#List_box := move _36#List_box
     end
     end;
     return _retv#List_box
    }>. 

Definition empty_list_func : function :=
  {| fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := None;
    fn_return := List_box;
    fn_callconv := cc_default;
    fn_vars := [(_retv, List_box); (_36, List_box); (_35, List_ty)];
    fn_params := [];
    fn_body := empty_list_body |}.

(* insert function *)

Definition insert_body : statement :=
  <{ let head: Node_ty in
  let _37: Node_ty in
  _37#Node_ty proj key<type_int32s> := copy k#type_int32s;
  _37#Node_ty proj val<type_int32s> := copy v#type_int32s;
  _37#Node_ty proj next<List_box> := move l#List_box;
  head#Node_ty := move _37#Node_ty
  end 
  end;
  let _39: List_box in
  let _38: List_ty in
  _38#List_ty :=v List::Cons(move head#Node_ty);
  _39#List_box :=b move _38#List_ty; 
  l#List_box := move _39#List_box
  end
  end;
  _retv#List_box := move l#List_box;
  return _retv#List_box }>.

Definition insert_func : function :=
  {| fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := None;
    fn_return := List_box;
    fn_callconv := cc_default;
    fn_vars := [(_retv, List_box); (head, Node_ty); (_37, Node_ty); (_39, List_box); (_38, List_ty)];
    fn_params := [];
    fn_body := insert_body |}.
  
(* remove function *)

Definition remove_ty : type :=
  Tfunction nil nil (Tcons List_box (Tcons type_int32s Tnil)) List_box cc_default.

Definition remove_body : statement :=
  <{ if (cktag l#List_ty is Nil) then
       let wildcard : Tunit in
         wildcard#Tunit := copy (!l#List_box) as Nil <Tunit>;
         _retv#List_box := move l#List_box;
         return _retv#List_box
       end
     else
       let node : Node_ty in
         node#Node_ty := move (!l#List_box) as Cons <Node_ty>;
         if (copy k#type_int32s == copy node#Node_ty proj key<type_int32s>) then
           _retv#List_box := move (l#List_box proj next <List_box>);
           return _retv#List_box
         else
           let _40 : List_box in
             _40#List_box <- remove<remove_ty> @ {move node#Node_ty proj next<List_box>, pure (copy k#type_int32s)};
             node#Node_ty proj next<List_box> := move _40#List_box
           end;
           let _41 : List_ty in
             _41#List_ty :=v List::Cons(move node#Node_ty); 
             (!l#List_box) := move _41#List_ty
           end;
           _retv#List_box := move l#List_box;
           return _retv#List_box
         fi
        end
      fi }>.

Definition remove_func : function :=
  {| fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := None;
    fn_return := List_box;
    fn_callconv := cc_default;
    fn_vars := [(_retv, List_box); (wildcard, Tunit); (node, Node_ty); (_40, List_box); (_41, List_ty)];
    fn_params := [(l, List_box); (k, type_int32s)];
    fn_body := remove_body |}.

(* drop glues *)

Definition drop_in_place_Node : function :=
    {| fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := Some Node;
    fn_return := Tunit;
    fn_callconv := cc_default;
    fn_vars := [];
    fn_params := [];
    fn_body := Sskip |}.

Definition drop_in_place_List : function :=
    {| fn_generic_origins := nil;
    fn_origins_relation := nil;
    fn_drop_glue := Some List;
    fn_return := Tunit;
    fn_callconv := cc_default;
    fn_vars := [];
    fn_params := [];
    fn_body := Sskip |}.

(* composite definitions *)

Definition Node_members := [Member_plain key type_int32s; Member_plain val (Tbox type_int32s); Member_plain next List_box].

Definition composite_types : list composite_definition :=
  (* Node *)
  Composite Node Struct Node_members nil nil ::
  (* List *)
  Composite List TaggedUnion [Member_plain Nil Tunit; Member_plain Cons Node_ty] nil nil ::
  nil.

Lemma build_ce_ok :
  { ce | build_composite_env composite_types = OK ce}.
Proof.
  eexists. unfold build_composite_env, composite_types. simpl. eauto.
Defined.

(* external functions *)

Definition process_ext : fundef :=
  External nil nil (EF_external "process" (AST.mksignature [AST.Tlong] AST.Tlong cc_default)) (Tcons (Tbox type_int32s) Tnil) (Tbox type_int32s) cc_default.

Definition linked_list_mod : program :=
  {| prog_defs := [(hash, Gfun (Internal hash_func));
                   (find, Gfun (Internal find_func));
                   (* (empty_list, Gfun (Internal empty_list_func)); *)
                   (* (insert, Gfun (Internal insert_func)); *)
                   (* (remove, Gfun (Internal remove_func)); *)
                   (process, Gfun process_ext);
                   (__drop_in_place_Node, Gfun (Internal (drop_in_place_Node)));
                   (__drop_in_place_List, Gfun (Internal (drop_in_place_List)));
                   (* malloc and free place holders. No need to specify its argument types *)
                   (malloc, Gfun (External [] [] AST.EF_malloc Tnil Tunit cc_default));
                   (free, Gfun (External [] [] AST.EF_free Tnil Tunit cc_default))];
    prog_public := [hash; find; (* empty_list; insert; remove; *) process; malloc; free];
    prog_main := 201%positive;
    prog_types := composite_types;
    prog_comp_env := proj1_sig build_ce_ok;
    prog_comp_env_eq := proj2_sig build_ce_ok; |}.


(* Compute (sizeof (prog_comp_env linked_list_mod) (Tstruct nil List)). *)
(* Compute (field_offset (prog_comp_env linked_list_mod) val Node_members). *)
(* Compute (field_offset (prog_comp_env linked_list_mod) next Node_members). *)
