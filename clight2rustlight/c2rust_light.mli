
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type sumbool =
| Left
| Right

val max : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size : positive -> positive

  val compare_cont :
    comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val testbit : positive -> n -> bool

  val of_succ_nat : nat -> positive

  val eq_dec : positive -> positive -> sumbool
 end

module N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val succ_pos : n -> positive

  val sub : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val pos_div_eucl : positive -> n -> (n, n) prod

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val ldiff : n -> n -> n

  val coq_lxor : n -> n -> n

  val testbit : n -> n -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val pred : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val max : z -> z -> z

  val of_nat : nat -> z

  val of_N : n -> z

  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val modulo : z -> z -> z

  val quotrem : z -> z -> (z, z) prod

  val quot : z -> z -> z

  val rem : z -> z -> z

  val odd : z -> bool

  val div2 : z -> z

  val log2 : z -> z

  val testbit : z -> z -> bool

  val shiftl : z -> z -> z

  val shiftr : z -> z -> z

  val coq_lor : z -> z -> z

  val coq_land : z -> z -> z

  val coq_lxor : z -> z -> z

  val eq_dec : z -> z -> sumbool
 end

val z_lt_dec : z -> z -> sumbool

val z_le_dec : z -> z -> sumbool

val z_le_gt_dec : z -> z -> sumbool

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * 
   bool * bool

type string =
| EmptyString
| String of ascii * string

val shift_nat : nat -> positive -> positive

val shift_pos : positive -> positive -> positive

val two_power_nat : nat -> z

val two_power_pos : positive -> z

val two_p : z -> z

val zeq : z -> z -> sumbool

val zlt : z -> z -> sumbool

val zle : z -> z -> sumbool

val align : z -> z -> z

val proj_sumbool : sumbool -> bool

type errcode =
| MSG of string
| CTX of positive
| POS of positive

type errmsg = errcode list

val msg : string -> errmsg

type 'a res =
| OK of 'a
| Error of errmsg

val bind : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res

module PTree :
 sig
  type 'a tree' =
  | Node001 of 'a tree'
  | Node010 of 'a
  | Node011 of 'a * 'a tree'
  | Node100 of 'a tree'
  | Node101 of 'a tree' * 'a tree'
  | Node110 of 'a tree' * 'a
  | Node111 of 'a tree' * 'a * 'a tree'

  type 'a tree =
  | Empty
  | Nodes of 'a tree'

  type 'a t = 'a tree

  val empty : 'a1 t

  val get' : positive -> 'a1 tree' -> 'a1 option

  val get : positive -> 'a1 tree -> 'a1 option

  val set0 : positive -> 'a1 -> 'a1 tree'

  val set' : positive -> 'a1 -> 'a1 tree' -> 'a1 tree'

  val set : positive -> 'a1 -> 'a1 tree -> 'a1 tree
 end

val p_mod_two_p : positive -> nat -> z

val zshiftin : bool -> z -> z

val zzero_ext : z -> z -> z

val zsign_ext : z -> z -> z

val z_one_bits : nat -> z -> z -> z list

val p_is_power2 : positive -> bool

val z_is_power2 : z -> z option

val zsize : z -> z

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * positive
| B754_finite of bool * positive * z

type binary32 = binary_float

type binary64 = binary_float

val ptr64 : bool

val align_int64 : z

val align_float64 : z

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int =
    z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> sumbool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int, int) prod option

  val divmods2 : int -> int -> int -> (int, int) prod option

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : nat
 end

module Int :
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int =
    z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> sumbool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int, int) prod option

  val divmods2 : int -> int -> int -> (int, int) prod option

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Int64 :
 sig
  type int =
    z
    (* singleton inductive, whose constructor was mkint *)
 end

module Ptrofs :
 sig
  type int =
    z
    (* singleton inductive, whose constructor was mkint *)
 end

type float = binary64

type float32 = binary32

type ident = positive

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

type rettype =
| Tret of typ
| Tint8signed
| Tint8unsigned
| Tint16signed
| Tint16unsigned
| Tvoid

type calling_convention = { cc_vararg : z option;
                            cc_unproto : bool;
                            cc_structret : bool }

type signature = { sig_args : typ list; sig_res : rettype;
                   sig_cc : calling_convention }

type memory_chunk =
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

type init_data =
| Init_int8 of Int.int
| Init_int16 of Int.int
| Init_int32 of Int.int
| Init_int64 of Int64.int
| Init_float32 of float32
| Init_float64 of float
| Init_space of z
| Init_addrof of ident * Ptrofs.int

type 'v globvar = { gvar_info : 'v;
                    gvar_init : init_data list;
                    gvar_readonly : bool; gvar_volatile : 
                    bool }

type ('f, 'v) globdef =
| Gfun of 'f
| Gvar of 'v globvar

type ('f, 'v) program = { prog_defs : (ident, ('f, 'v)
                                      globdef) prod list;
                          prog_public : ident list;
                          prog_main : ident }

val transf_globvar :
  (ident -> 'a1 -> 'a2 res) -> ident -> 'a1 globvar -> 'a2
  globvar res

val transf_globdefs :
  (ident -> 'a1 -> 'a2 res) -> (ident -> 'a3 -> 'a4 res) ->
  (ident, ('a1, 'a3) globdef) prod list -> (ident, ('a2, 'a4)
  globdef) prod list res

val transform_partial_program2 :
  (ident -> 'a1 -> 'a2 res) -> (ident -> 'a3 -> 'a4 res) ->
  ('a1, 'a3) program -> ('a2, 'a4) program res

type external_function =
| EF_external of string * signature
| EF_builtin of string * signature
| EF_runtime of string * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_malloc
| EF_free
| EF_memcpy of z * z
| EF_annot of positive * string * typ list
| EF_annot_val of positive * string * typ
| EF_inline_asm of string * signature * string list
| EF_debug of positive * ident * typ list

type signedness =
| Signed
| Unsigned

type intsize =
| I8
| I16
| I32
| IBool

type floatsize =
| F32
| F64

type attr = { attr_volatile : bool; attr_alignas : n option }

type type0 =
| Tvoid0
| Tint0 of intsize * signedness * attr
| Tlong0 of signedness * attr
| Tfloat0 of floatsize * attr
| Tpointer of type0 * attr
| Tarray of type0 * z * attr
| Tfunction of typelist * type0 * calling_convention
| Tstruct of ident * attr
| Tunion of ident * attr
and typelist =
| Tnil
| Tcons of type0 * typelist

type struct_or_union =
| Struct
| Union

type member =
| Member_plain of ident * type0
| Member_bitfield of ident * intsize * signedness * attr * 
   z * bool

type members = member list

type composite_definition =
| Composite of ident * struct_or_union * members * attr

type composite = { co_su : struct_or_union;
                   co_members : members; co_attr : attr;
                   co_sizeof : z; co_alignof : z;
                   co_rank : nat }

type composite_env = composite PTree.t

val bytes_of_bits : z -> z

type 'f fundef =
| Internal of 'f
| External of external_function * typelist * type0
   * calling_convention

type 'f program0 = { prog_defs0 : (ident, ('f fundef, type0)
                                  globdef) prod list;
                     prog_public0 : ident list;
                     prog_main0 : ident;
                     prog_types : composite_definition list;
                     prog_comp_env : composite_env }

val program_of_program :
  'a1 program0 -> ('a1 fundef, type0) program

type mutkind =
| Mutable
| Immutable

type origin = positive

type origin_rel = (origin, origin) prod

type type1 =
| Tunit
| Tint1 of intsize * signedness
| Tlong1 of signedness
| Tfloat1 of floatsize
| Tfunction0 of origin list * origin_rel list * typelist0
   * type1 * calling_convention
| Tbox of type1
| Treference of origin * mutkind * type1
| Tarray0 of type1 * z
| Tstruct0 of origin list * ident
| Tvariant of origin list * ident
and typelist0 =
| Tnil0
| Tcons0 of type1 * typelist0

val type_int32s : type1

type struct_or_variant =
| Struct0
| TaggedUnion

type member0 =
| Member_plain0 of ident * type1

type members0 = member0 list

type composite_definition0 =
| Composite0 of ident * struct_or_variant * members0
   * origin list * origin_rel list

val type_member : member0 -> type1

type composite0 = { co_generic_origins : origin list;
                    co_origin_relations : origin_rel list;
                    co_sv : struct_or_variant;
                    co_members0 : members0; co_sizeof0 : 
                    z; co_alignof0 : z; co_rank0 : nat }

type composite_env0 = composite0 PTree.t

val complete_type : composite_env0 -> type1 -> bool

val alignof : composite_env0 -> type1 -> z

val sizeof : composite_env0 -> type1 -> z

val bitalignof : composite_env0 -> type1 -> z

val bitsizeof : composite_env0 -> type1 -> z

val next_field : composite_env0 -> z -> member0 -> z

val alignof_composite' : composite_env0 -> members0 -> z

val alignof_composite :
  composite_env0 -> struct_or_variant -> members0 -> z

val bitsizeof_struct : composite_env0 -> z -> members0 -> z

val sizeof_struct : composite_env0 -> members0 -> z

val sizeof_variant' : composite_env0 -> members0 -> z

val sizeof_variant : composite_env0 -> members0 -> z

val rank_type : composite_env0 -> type1 -> nat

val rank_members : composite_env0 -> members0 -> nat

val sizeof_composite :
  composite_env0 -> struct_or_variant -> members0 -> z

val complete_members : composite_env0 -> members0 -> bool

val composite_of_def :
  composite_env0 -> ident -> struct_or_variant -> members0 ->
  origin list -> origin_rel list -> composite0 res

val add_composite_definitions :
  composite_env0 -> composite_definition0 list ->
  composite_env0 res

val build_composite_env :
  composite_definition0 list -> composite_env0 res

type 'f fundef0 =
| Internal0 of 'f
| External0 of origin list * origin_rel list
   * external_function * typelist0 * type1
   * calling_convention

type 'f program1 = { prog_defs1 : (ident, ('f fundef0, type1)
                                  globdef) prod list;
                     prog_public1 : ident list;
                     prog_main1 : ident;
                     prog_types0 : composite_definition0 list;
                     prog_comp_env0 : composite_env0 }

type unary_operation =
| Onotbool
| Onotint
| Oneg
| Oabsfloat

type binary_operation =
| Oadd
| Osub
| Omul
| Odiv
| Omod
| Oand
| Oor
| Oxor
| Oshl
| Oshr
| Oeq
| One
| Olt
| Ogt
| Ole
| Oge

type expr =
| Econst_int of Int.int * type0
| Econst_float of float * type0
| Econst_single of float32 * type0
| Econst_long of Int64.int * type0
| Evar of ident * type0
| Etempvar of ident * type0
| Ederef of expr * type0
| Eaddrof of expr * type0
| Eunop of unary_operation * expr * type0
| Ebinop of binary_operation * expr * expr * type0
| Ecast of expr * type0
| Efield of expr * ident * type0
| Esizeof of type0 * type0
| Ealignof of type0 * type0

val typeof : expr -> type0

type label = ident

type statement =
| Sskip
| Sassign of expr * expr
| Sset of ident * expr
| Scall of ident option * expr * expr list
| Sbuiltin of ident option * external_function * typelist
   * expr list
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Sloop of statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of z option * statement * labeled_statements

type function0 = { fn_return : type0;
                   fn_callconv : calling_convention;
                   fn_params : (ident, type0) prod list;
                   fn_vars : (ident, type0) prod list;
                   fn_temps : (ident, type0) prod list;
                   fn_body : statement }

type fundef1 = function0 fundef

type program2 = function0 program0

type place =
| Plocal of ident * type1
| Pfield of place * ident * type1
| Pderef of place * type1
| Pdowncast of place * ident * type1

type pexpr =
| Eunit
| Econst_int0 of Int.int * type1
| Econst_float0 of float * type1
| Econst_single0 of float32 * type1
| Econst_long0 of Int64.int * type1
| Eplace of place * type1
| Ecktag of place * ident
| Eref of origin * mutkind * place * type1
| Eunop0 of unary_operation * pexpr * type1
| Ebinop0 of binary_operation * pexpr * pexpr * type1
| Eglobal of ident * type1

type expr0 =
| Emoveplace of place * type1
| Epure of pexpr

type statement0 =
| Sskip0
| Slet of ident * type1 * statement0
| Sassign0 of place * expr0
| Sassign_variant of place * ident * ident * expr0
| Sbox of place * expr0
| Scall0 of place * expr0 * expr0 list
| Ssequence0 of statement0 * statement0
| Sifthenelse0 of expr0 * statement0 * statement0
| Sloop0 of statement0
| Sbreak0
| Scontinue0
| Sreturn0 of place

type function1 = { fn_generic_origins : origin list;
                   fn_origins_relation : (origin, origin)
                                         prod list;
                   fn_drop_glue : ident option;
                   fn_return0 : type1;
                   fn_callconv0 : calling_convention;
                   fn_vars0 : (ident, type1) prod list;
                   fn_params0 : (ident, type1) prod list;
                   fn_body0 : statement0 }

type fundef2 = function1 fundef0

type program3 = function1 program1

val to_rusttype : type0 -> type1

val to_rustlight : typelist -> typelist0

val cexpr_to_place : expr -> place res

val cexpr_to_pexpr : expr -> pexpr res

val transl_expr_list : expr list -> pexpr list res

val pexpr_to_expr : pexpr -> expr0

val empty_place : place

val transl_stmt : statement -> statement0 res

val transl_function : function0 -> function1 res

val transl_fundef : ident -> fundef1 -> fundef2 res

val transl_globvar : ident -> type0 -> type1 res

val convert_members : members -> members0 res

val convert_composite_definition :
  composite_definition list -> composite_definition0 list res

val transl_program : program2 -> program3 res
