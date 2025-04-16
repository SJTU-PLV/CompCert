
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type sumbool =
| Left
| Right

(** val max : nat -> nat -> nat **)

let rec max n0 m =
  match n0 with
  | O -> m
  | S n' -> (match m with
             | O -> n0
             | S m' -> S (max n' m'))

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

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont :
      comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> True
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> False
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH -> (match n0 with
             | N0 -> True
             | Npos _ -> False)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 ->
      (match x0 with
       | XI p1 -> eq_dec p0 p1
       | _ -> Right)
    | XO p0 ->
      (match x0 with
       | XO p1 -> eq_dec p0 p1
       | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' ->
      (match m with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)

  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> False
    | Npos p -> Coq_Pos.testbit p n0
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Eq
       | Zpos _ -> Lt
       | Zneg _ -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Coq_Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter f x p
    | _ -> x

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False ->
         Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)),
           (sub r' b)))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False ->
         Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)),
           (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, Z0)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         Pair (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> (z, z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (of_N r))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> False
  | Zpos p -> (match p with
               | XO _ -> False
               | _ -> True)
  | Zneg p -> (match p with
               | XO _ -> False
               | _ -> True)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)

  (** val log2 : z -> z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0

  (** val testbit : z -> z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> False
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 ->
       negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg _ -> False

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Coq_Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 ->
         Zneg
           (N.succ_pos
             (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg
           (N.succ_pos
             (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg
           (N.succ_pos
             (N.coq_land (Coq_Pos.pred_N a0)
               (Coq_Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 ->
         of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 ->
         of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 ->
         Zneg
           (N.succ_pos
             (N.coq_lor (Coq_Pos.pred_N a0)
               (Coq_Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 ->
         Zneg
           (N.succ_pos
             (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg
           (N.succ_pos
             (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         of_N
           (N.coq_lxor (Coq_Pos.pred_N a0)
             (Coq_Pos.pred_N b0)))

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos x0 ->
      (match y with
       | Zpos p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> Right)
    | Zneg x0 ->
      (match y with
       | Zneg p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> Right)
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_le_dec : z -> z -> sumbool **)

let z_le_dec x y =
  match Z.compare x y with
  | Gt -> Right
  | _ -> Left

(** val z_le_gt_dec : z -> z -> sumbool **)

let z_le_gt_dec =
  z_le_dec

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * 
   bool * bool

type string =
| EmptyString
| String of ascii * string

(** val shift_nat : nat -> positive -> positive **)

let rec shift_nat n0 z0 =
  match n0 with
  | O -> z0
  | S n1 -> XO (shift_nat n1 z0)

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n0 z0 =
  Coq_Pos.iter (fun x -> XO x) z0 n0

(** val two_power_nat : nat -> z **)

let two_power_nat n0 =
  Zpos (shift_nat n0 XH)

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val two_p : z -> z **)

let two_p = function
| Z0 -> Zpos XH
| Zpos y -> two_power_pos y
| Zneg _ -> Z0

(** val zeq : z -> z -> sumbool **)

let zeq =
  Z.eq_dec

(** val zlt : z -> z -> sumbool **)

let zlt =
  z_lt_dec

(** val zle : z -> z -> sumbool **)

let zle =
  z_le_gt_dec

(** val align : z -> z -> z **)

let align n0 amount =
  Z.mul (Z.div (Z.sub (Z.add n0 amount) (Zpos XH)) amount)
    amount

(** val proj_sumbool : sumbool -> bool **)

let proj_sumbool = function
| Left -> True
| Right -> False

type errcode =
| MSG of string
| CTX of positive
| POS of positive

type errmsg = errcode list

(** val msg : string -> errmsg **)

let msg s =
  Cons ((MSG s), Nil)

type 'a res =
| OK of 'a
| Error of errmsg

(** val bind : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res **)

let bind f g =
  match f with
  | OK x -> g x
  | Error msg0 -> Error msg0

module PTree =
 struct
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

  (** val empty : 'a1 t **)

  let empty =
    Empty

  (** val get' : positive -> 'a1 tree' -> 'a1 option **)

  let rec get' p m =
    match p with
    | XI q ->
      (match m with
       | Node001 m' -> get' q m'
       | Node011 (_, m') -> get' q m'
       | Node101 (_, m') -> get' q m'
       | Node111 (_, _, m') -> get' q m'
       | _ -> None)
    | XO q ->
      (match m with
       | Node100 m' -> get' q m'
       | Node101 (m', _) -> get' q m'
       | Node110 (m', _) -> get' q m'
       | Node111 (m', _, _) -> get' q m'
       | _ -> None)
    | XH ->
      (match m with
       | Node010 x -> Some x
       | Node011 (x, _) -> Some x
       | Node110 (_, x) -> Some x
       | Node111 (_, x, _) -> Some x
       | _ -> None)

  (** val get : positive -> 'a1 tree -> 'a1 option **)

  let get p = function
  | Empty -> None
  | Nodes m' -> get' p m'

  (** val set0 : positive -> 'a1 -> 'a1 tree' **)

  let rec set0 p x =
    match p with
    | XI q -> Node001 (set0 q x)
    | XO q -> Node100 (set0 q x)
    | XH -> Node010 x

  (** val set' : positive -> 'a1 -> 'a1 tree' -> 'a1 tree' **)

  let rec set' p x m =
    match p with
    | XI q ->
      (match m with
       | Node001 r -> Node001 (set' q x r)
       | Node010 y -> Node011 (y, (set0 q x))
       | Node011 (y, r) -> Node011 (y, (set' q x r))
       | Node100 l -> Node101 (l, (set0 q x))
       | Node101 (l, r) -> Node101 (l, (set' q x r))
       | Node110 (l, y) -> Node111 (l, y, (set0 q x))
       | Node111 (l, y, r) -> Node111 (l, y, (set' q x r)))
    | XO q ->
      (match m with
       | Node001 r -> Node101 ((set0 q x), r)
       | Node010 y -> Node110 ((set0 q x), y)
       | Node011 (y, r) -> Node111 ((set0 q x), y, r)
       | Node100 l -> Node100 (set' q x l)
       | Node101 (l, r) -> Node101 ((set' q x l), r)
       | Node110 (l, y) -> Node110 ((set' q x l), y)
       | Node111 (l, y, r) -> Node111 ((set' q x l), y, r))
    | XH ->
      (match m with
       | Node001 r -> Node011 (x, r)
       | Node010 _ -> Node010 x
       | Node011 (_, r) -> Node011 (x, r)
       | Node100 l -> Node110 (l, x)
       | Node101 (l, r) -> Node111 (l, x, r)
       | Node110 (l, _) -> Node110 (l, x)
       | Node111 (l, _, r) -> Node111 (l, x, r))

  (** val set : positive -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let set p x = function
  | Empty -> Nodes (set0 p x)
  | Nodes m' -> Nodes (set' p x m')
 end

(** val p_mod_two_p : positive -> nat -> z **)

let rec p_mod_two_p p = function
| O -> Z0
| S m ->
  (match p with
   | XI q -> Z.succ_double (p_mod_two_p q m)
   | XO q -> Z.double (p_mod_two_p q m)
   | XH -> Zpos XH)

(** val zshiftin : bool -> z -> z **)

let zshiftin b x =
  match b with
  | True -> Z.succ_double x
  | False -> Z.double x

(** val zzero_ext : z -> z -> z **)

let zzero_ext n0 x =
  Z.iter n0 (fun rec0 x0 ->
    zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun _ -> Z0) x

(** val zsign_ext : z -> z -> z **)

let zsign_ext n0 x =
  Z.iter (Z.pred n0) (fun rec0 x0 ->
    zshiftin (Z.odd x0) (rec0 (Z.div2 x0))) (fun x0 ->
    match match Z.odd x0 with
          | True -> proj_sumbool (zlt Z0 n0)
          | False -> False with
    | True -> Zneg XH
    | False -> Z0) x

(** val z_one_bits : nat -> z -> z -> z list **)

let rec z_one_bits n0 x i =
  match n0 with
  | O -> Nil
  | S m ->
    (match Z.odd x with
     | True ->
       Cons (i, (z_one_bits m (Z.div2 x) (Z.add i (Zpos XH))))
     | False -> z_one_bits m (Z.div2 x) (Z.add i (Zpos XH)))

(** val p_is_power2 : positive -> bool **)

let rec p_is_power2 = function
| XI _ -> False
| XO q -> p_is_power2 q
| XH -> True

(** val z_is_power2 : z -> z option **)

let z_is_power2 x = match x with
| Zpos p ->
  (match p_is_power2 p with
   | True -> Some (Z.log2 x)
   | False -> None)
| _ -> None

(** val zsize : z -> z **)

let zsize = function
| Zpos p -> Zpos (Coq_Pos.size p)
| _ -> Z0

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * positive
| B754_finite of bool * positive * z

type binary32 = binary_float

type binary64 = binary_float

(** val ptr64 : bool **)

let ptr64 =
  True

(** val align_int64 : z **)

let align_int64 =
  Zpos (XO (XO (XO XH)))

(** val align_float64 : z **)

let align_float64 =
  Zpos (XO (XO (XO XH)))

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

module Make =
 functor (WS:WORDSIZE) ->
 struct
  (** val wordsize : nat **)

  let wordsize =
    WS.wordsize

  (** val zwordsize : z **)

  let zwordsize =
    Z.of_nat wordsize

  (** val modulus : z **)

  let modulus =
    two_power_nat wordsize

  (** val half_modulus : z **)

  let half_modulus =
    Z.div modulus (Zpos (XO XH))

  (** val max_unsigned : z **)

  let max_unsigned =
    Z.sub modulus (Zpos XH)

  (** val max_signed : z **)

  let max_signed =
    Z.sub half_modulus (Zpos XH)

  (** val min_signed : z **)

  let min_signed =
    Z.opp half_modulus

  type int =
    z
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : int -> z **)

  let intval i =
    i

  (** val coq_Z_mod_modulus : z -> z **)

  let coq_Z_mod_modulus = function
  | Z0 -> Z0
  | Zpos p -> p_mod_two_p p wordsize
  | Zneg p ->
    let r = p_mod_two_p p wordsize in
    (match zeq r Z0 with
     | Left -> Z0
     | Right -> Z.sub modulus r)

  (** val unsigned : int -> z **)

  let unsigned =
    intval

  (** val signed : int -> z **)

  let signed n0 =
    let x = unsigned n0 in
    (match zlt x half_modulus with
     | Left -> x
     | Right -> Z.sub x modulus)

  (** val repr : z -> int **)

  let repr =
    coq_Z_mod_modulus

  (** val zero : int **)

  let zero =
    repr Z0

  (** val one : int **)

  let one =
    repr (Zpos XH)

  (** val mone : int **)

  let mone =
    repr (Zneg XH)

  (** val iwordsize : int **)

  let iwordsize =
    repr zwordsize

  (** val eq_dec : int -> int -> sumbool **)

  let eq_dec =
    zeq

  (** val eq : int -> int -> bool **)

  let eq x y =
    match zeq (unsigned x) (unsigned y) with
    | Left -> True
    | Right -> False

  (** val lt : int -> int -> bool **)

  let lt x y =
    match zlt (signed x) (signed y) with
    | Left -> True
    | Right -> False

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    match zlt (unsigned x) (unsigned y) with
    | Left -> True
    | Right -> False

  (** val neg : int -> int **)

  let neg x =
    repr (Z.opp (unsigned x))

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add (unsigned x) (unsigned y))

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub (unsigned x) (unsigned y))

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul (unsigned x) (unsigned y))

  (** val divs : int -> int -> int **)

  let divs x y =
    repr (Z.quot (signed x) (signed y))

  (** val mods : int -> int -> int **)

  let mods x y =
    repr (Z.rem (signed x) (signed y))

  (** val divu : int -> int -> int **)

  let divu x y =
    repr (Z.div (unsigned x) (unsigned y))

  (** val modu : int -> int -> int **)

  let modu x y =
    repr (Z.modulo (unsigned x) (unsigned y))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land (unsigned x) (unsigned y))

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor (unsigned x) (unsigned y))

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor (unsigned x) (unsigned y))

  (** val not : int -> int **)

  let not x =
    xor x mone

  (** val shl : int -> int -> int **)

  let shl x y =
    repr (Z.shiftl (unsigned x) (unsigned y))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr (Z.shiftr (unsigned x) (unsigned y))

  (** val shr : int -> int -> int **)

  let shr x y =
    repr (Z.shiftr (signed x) (unsigned y))

  (** val rol : int -> int -> int **)

  let rol x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftl (unsigned x) n0)
        (Z.shiftr (unsigned x) (Z.sub zwordsize n0)))

  (** val ror : int -> int -> int **)

  let ror x y =
    let n0 = Z.modulo (unsigned y) zwordsize in
    repr
      (Z.coq_lor (Z.shiftr (unsigned x) n0)
        (Z.shiftl (unsigned x) (Z.sub zwordsize n0)))

  (** val rolm : int -> int -> int -> int **)

  let rolm x a m =
    coq_and (rol x a) m

  (** val shrx : int -> int -> int **)

  let shrx x y =
    divs x (shl one y)

  (** val mulhu : int -> int -> int **)

  let mulhu x y =
    repr (Z.div (Z.mul (unsigned x) (unsigned y)) modulus)

  (** val mulhs : int -> int -> int **)

  let mulhs x y =
    repr (Z.div (Z.mul (signed x) (signed y)) modulus)

  (** val negative : int -> int **)

  let negative x =
    match lt x zero with
    | True -> one
    | False -> zero

  (** val add_carry : int -> int -> int -> int **)

  let add_carry x y cin =
    match zlt
            (Z.add (Z.add (unsigned x) (unsigned y))
              (unsigned cin)) modulus with
    | Left -> zero
    | Right -> one

  (** val add_overflow : int -> int -> int -> int **)

  let add_overflow x y cin =
    let s = Z.add (Z.add (signed x) (signed y)) (signed cin)
    in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val sub_borrow : int -> int -> int -> int **)

  let sub_borrow x y bin =
    match zlt
            (Z.sub (Z.sub (unsigned x) (unsigned y))
              (unsigned bin)) Z0 with
    | Left -> one
    | Right -> zero

  (** val sub_overflow : int -> int -> int -> int **)

  let sub_overflow x y bin =
    let s = Z.sub (Z.sub (signed x) (signed y)) (signed bin)
    in
    (match match proj_sumbool (zle min_signed s) with
           | True -> proj_sumbool (zle s max_signed)
           | False -> False with
     | True -> zero
     | False -> one)

  (** val shr_carry : int -> int -> int **)

  let shr_carry x y =
    match match lt x zero with
          | True ->
            negb (eq (coq_and x (sub (shl one y) one)) zero)
          | False -> False with
    | True -> one
    | False -> zero

  (** val zero_ext : z -> int -> int **)

  let zero_ext n0 x =
    repr (zzero_ext n0 (unsigned x))

  (** val sign_ext : z -> int -> int **)

  let sign_ext n0 x =
    repr (zsign_ext n0 (unsigned x))

  (** val one_bits : int -> int list **)

  let one_bits x =
    map repr (z_one_bits wordsize (unsigned x) Z0)

  (** val is_power2 : int -> int option **)

  let is_power2 x =
    match z_is_power2 (unsigned x) with
    | Some i -> Some (repr i)
    | None -> None

  (** val cmp : comparison0 -> int -> int -> bool **)

  let cmp c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> lt x y
    | Cle -> negb (lt y x)
    | Cgt -> lt y x
    | Cge -> negb (lt x y)

  (** val cmpu : comparison0 -> int -> int -> bool **)

  let cmpu c x y =
    match c with
    | Ceq -> eq x y
    | Cne -> negb (eq x y)
    | Clt -> ltu x y
    | Cle -> negb (ltu y x)
    | Cgt -> ltu y x
    | Cge -> negb (ltu x y)

  (** val notbool : int -> int **)

  let notbool x =
    match eq x zero with
    | True -> one
    | False -> zero

  (** val divmodu2 :
      int -> int -> int -> (int, int) prod option **)

  let divmodu2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r) =
        Z.div_eucl
          (Z.add (Z.mul (unsigned nhi) modulus)
            (unsigned nlo)) (unsigned d)
      in
      (match zle q max_unsigned with
       | Left -> Some (Pair ((repr q), (repr r)))
       | Right -> None)

  (** val divmods2 :
      int -> int -> int -> (int, int) prod option **)

  let divmods2 nhi nlo d =
    match eq_dec d zero with
    | Left -> None
    | Right ->
      let Pair (q, r) =
        Z.quotrem
          (Z.add (Z.mul (signed nhi) modulus) (unsigned nlo))
          (signed d)
      in
      (match match proj_sumbool (zle min_signed q) with
             | True -> proj_sumbool (zle q max_signed)
             | False -> False with
       | True -> Some (Pair ((repr q), (repr r)))
       | False -> None)

  (** val testbit : int -> z -> bool **)

  let testbit x i =
    Z.testbit (unsigned x) i

  (** val int_of_one_bits : int list -> int **)

  let rec int_of_one_bits = function
  | Nil -> zero
  | Cons (a, b) -> add (shl one a) (int_of_one_bits b)

  (** val no_overlap : int -> z -> int -> z -> bool **)

  let no_overlap ofs1 sz1 ofs2 sz2 =
    let x1 = unsigned ofs1 in
    let x2 = unsigned ofs2 in
    (match match proj_sumbool (zlt (Z.add x1 sz1) modulus) with
           | True -> proj_sumbool (zlt (Z.add x2 sz2) modulus)
           | False -> False with
     | True ->
       (match proj_sumbool (zle (Z.add x1 sz1) x2) with
        | True -> True
        | False -> proj_sumbool (zle (Z.add x2 sz2) x1))
     | False -> False)

  (** val size : int -> z **)

  let size x =
    zsize (unsigned x)

  (** val unsigned_bitfield_extract : z -> z -> int -> int **)

  let unsigned_bitfield_extract pos width n0 =
    zero_ext width (shru n0 (repr pos))

  (** val signed_bitfield_extract : z -> z -> int -> int **)

  let signed_bitfield_extract pos width n0 =
    sign_ext width (shru n0 (repr pos))

  (** val bitfield_insert : z -> z -> int -> int -> int **)

  let bitfield_insert pos width n0 p =
    let mask0 =
      shl (repr (Z.sub (two_p width) (Zpos XH))) (repr pos)
    in
    coq_or (shl (zero_ext width p) (repr pos))
      (coq_and n0 (not mask0))
 end

module Wordsize_32 =
 struct
  (** val wordsize : nat **)

  let wordsize =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))
 end

module Int = Make(Wordsize_32)

module Int64 =
 struct
  type int =
    z
    (* singleton inductive, whose constructor was mkint *)
 end

module Ptrofs =
 struct
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

(** val transf_globvar :
    (ident -> 'a1 -> 'a2 res) -> ident -> 'a1 globvar -> 'a2
    globvar res **)

let transf_globvar transf_var i g =
  bind (transf_var i g.gvar_info) (fun info' -> OK
    { gvar_info = info'; gvar_init = g.gvar_init;
    gvar_readonly = g.gvar_readonly; gvar_volatile =
    g.gvar_volatile })

(** val transf_globdefs :
    (ident -> 'a1 -> 'a2 res) -> (ident -> 'a3 -> 'a4 res) ->
    (ident, ('a1, 'a3) globdef) prod list -> (ident, ('a2,
    'a4) globdef) prod list res **)

let rec transf_globdefs transf_fun transf_var = function
| Nil -> OK Nil
| Cons (p, l') ->
  let Pair (id, g) = p in
  (match g with
   | Gfun f ->
     (match transf_fun id f with
      | OK tf ->
        bind (transf_globdefs transf_fun transf_var l')
          (fun tl' -> OK (Cons ((Pair (id, (Gfun tf))), tl')))
      | Error msg0 ->
        Error (Cons ((MSG (String ((Ascii (True, False,
          False, True, False, False, True, False)), (String
          ((Ascii (False, True, True, True, False, True,
          True, False)), (String ((Ascii (False, False,
          False, False, False, True, False, False)), (String
          ((Ascii (False, True, True, False, False, True,
          True, False)), (String ((Ascii (True, False, True,
          False, True, True, True, False)), (String ((Ascii
          (False, True, True, True, False, True, True,
          False)), (String ((Ascii (True, True, False, False,
          False, True, True, False)), (String ((Ascii (False,
          False, True, False, True, True, True, False)),
          (String ((Ascii (True, False, False, True, False,
          True, True, False)), (String ((Ascii (True, True,
          True, True, False, True, True, False)), (String
          ((Ascii (False, True, True, True, False, True,
          True, False)), (String ((Ascii (False, False,
          False, False, False, True, False, False)),
          EmptyString))))))))))))))))))))))))), (Cons ((CTX
          id), (Cons ((MSG (String ((Ascii (False, True,
          False, True, True, True, False, False)), (String
          ((Ascii (False, False, False, False, False, True,
          False, False)), EmptyString))))), msg0)))))))
   | Gvar v ->
     (match transf_globvar transf_var id v with
      | OK tv ->
        bind (transf_globdefs transf_fun transf_var l')
          (fun tl' -> OK (Cons ((Pair (id, (Gvar tv))), tl')))
      | Error msg0 ->
        Error (Cons ((MSG (String ((Ascii (True, False,
          False, True, False, False, True, False)), (String
          ((Ascii (False, True, True, True, False, True,
          True, False)), (String ((Ascii (False, False,
          False, False, False, True, False, False)), (String
          ((Ascii (False, True, True, False, True, True,
          True, False)), (String ((Ascii (True, False, False,
          False, False, True, True, False)), (String ((Ascii
          (False, True, False, False, True, True, True,
          False)), (String ((Ascii (True, False, False, True,
          False, True, True, False)), (String ((Ascii (True,
          False, False, False, False, True, True, False)),
          (String ((Ascii (False, True, False, False, False,
          True, True, False)), (String ((Ascii (False, False,
          True, True, False, True, True, False)), (String
          ((Ascii (True, False, True, False, False, True,
          True, False)), (String ((Ascii (False, False,
          False, False, False, True, False, False)),
          EmptyString))))))))))))))))))))))))), (Cons ((CTX
          id), (Cons ((MSG (String ((Ascii (False, True,
          False, True, True, True, False, False)), (String
          ((Ascii (False, False, False, False, False, True,
          False, False)), EmptyString))))), msg0))))))))

(** val transform_partial_program2 :
    (ident -> 'a1 -> 'a2 res) -> (ident -> 'a3 -> 'a4 res) ->
    ('a1, 'a3) program -> ('a2, 'a4) program res **)

let transform_partial_program2 transf_fun transf_var p =
  bind (transf_globdefs transf_fun transf_var p.prog_defs)
    (fun gl' -> OK { prog_defs = gl'; prog_public =
    p.prog_public; prog_main = p.prog_main })

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

(** val bytes_of_bits : z -> z **)

let bytes_of_bits n0 =
  Z.div (Z.add n0 (Zpos (XI (XI XH)))) (Zpos (XO (XO (XO
    XH))))

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

(** val program_of_program :
    'a1 program0 -> ('a1 fundef, type0) program **)

let program_of_program p =
  { prog_defs = p.prog_defs0; prog_public = p.prog_public0;
    prog_main = p.prog_main0 }

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

(** val type_int32s : type1 **)

let type_int32s =
  Tint1 (I32, Signed)

type struct_or_variant =
| Struct0
| TaggedUnion

type member0 =
| Member_plain0 of ident * type1

type members0 = member0 list

type composite_definition0 =
| Composite0 of ident * struct_or_variant * members0
   * origin list * origin_rel list

(** val type_member : member0 -> type1 **)

let type_member = function
| Member_plain0 (_, t0) -> t0

type composite0 = { co_generic_origins : origin list;
                    co_origin_relations : origin_rel list;
                    co_sv : struct_or_variant;
                    co_members0 : members0; co_sizeof0 : 
                    z; co_alignof0 : z; co_rank0 : nat }

type composite_env0 = composite0 PTree.t

(** val complete_type : composite_env0 -> type1 -> bool **)

let rec complete_type env = function
| Tfunction0 (_, _, _, _, _) -> False
| Tarray0 (t', _) -> complete_type env t'
| Tstruct0 (_, id) ->
  (match PTree.get id env with
   | Some _ -> True
   | None -> False)
| Tvariant (_, id) ->
  (match PTree.get id env with
   | Some _ -> True
   | None -> False)
| _ -> True

(** val alignof : composite_env0 -> type1 -> z **)

let rec alignof env = function
| Tunit -> Zpos (XO (XO XH))
| Tint1 (i, _) ->
  (match i with
   | I16 -> Zpos (XO XH)
   | I32 -> Zpos (XO (XO XH))
   | _ -> Zpos XH)
| Tlong1 _ -> align_int64
| Tfloat1 f ->
  (match f with
   | F32 -> Zpos (XO (XO XH))
   | F64 -> align_float64)
| Tfunction0 (_, _, _, _, _) -> Zpos XH
| Tarray0 (t', _) -> alignof env t'
| Tstruct0 (_, id) ->
  (match PTree.get id env with
   | Some co -> co.co_alignof0
   | None -> Zpos XH)
| Tvariant (_, id) ->
  (match PTree.get id env with
   | Some co -> co.co_alignof0
   | None -> Zpos XH)
| _ ->
  (match ptr64 with
   | True -> Zpos (XO (XO (XO XH)))
   | False -> Zpos (XO (XO XH)))

(** val sizeof : composite_env0 -> type1 -> z **)

let rec sizeof env = function
| Tunit -> Zpos (XO (XO XH))
| Tint1 (i, _) ->
  (match i with
   | I16 -> Zpos (XO XH)
   | I32 -> Zpos (XO (XO XH))
   | _ -> Zpos XH)
| Tlong1 _ -> Zpos (XO (XO (XO XH)))
| Tfloat1 f ->
  (match f with
   | F32 -> Zpos (XO (XO XH))
   | F64 -> Zpos (XO (XO (XO XH))))
| Tfunction0 (_, _, _, _, _) -> Zpos XH
| Tarray0 (t', n0) -> Z.mul (sizeof env t') (Z.max Z0 n0)
| Tstruct0 (_, id) ->
  (match PTree.get id env with
   | Some co -> co.co_sizeof0
   | None -> Z0)
| Tvariant (_, id) ->
  (match PTree.get id env with
   | Some co -> co.co_sizeof0
   | None -> Z0)
| _ ->
  (match ptr64 with
   | True -> Zpos (XO (XO (XO XH)))
   | False -> Zpos (XO (XO XH)))

(** val bitalignof : composite_env0 -> type1 -> z **)

let bitalignof env t0 =
  Z.mul (alignof env t0) (Zpos (XO (XO (XO XH))))

(** val bitsizeof : composite_env0 -> type1 -> z **)

let bitsizeof env t0 =
  Z.mul (sizeof env t0) (Zpos (XO (XO (XO XH))))

(** val next_field : composite_env0 -> z -> member0 -> z **)

let next_field env pos = function
| Member_plain0 (_, t0) ->
  Z.add (align pos (bitalignof env t0)) (bitsizeof env t0)

(** val alignof_composite' :
    composite_env0 -> members0 -> z **)

let rec alignof_composite' env = function
| Nil -> Zpos XH
| Cons (m, ms0) ->
  Z.max (alignof env (type_member m))
    (alignof_composite' env ms0)

(** val alignof_composite :
    composite_env0 -> struct_or_variant -> members0 -> z **)

let alignof_composite env sv ms =
  match sv with
  | Struct0 -> alignof_composite' env ms
  | TaggedUnion ->
    Z.max (alignof env type_int32s)
      (alignof_composite' env ms)

(** val bitsizeof_struct :
    composite_env0 -> z -> members0 -> z **)

let rec bitsizeof_struct env cur = function
| Nil -> cur
| Cons (m, ms0) ->
  bitsizeof_struct env (next_field env cur m) ms0

(** val sizeof_struct : composite_env0 -> members0 -> z **)

let sizeof_struct env m =
  bytes_of_bits (bitsizeof_struct env Z0 m)

(** val sizeof_variant' : composite_env0 -> members0 -> z **)

let rec sizeof_variant' env = function
| Nil -> Z0
| Cons (m, ms0) ->
  Z.max (sizeof env (type_member m)) (sizeof_variant' env ms0)

(** val sizeof_variant : composite_env0 -> members0 -> z **)

let sizeof_variant env ms =
  bytes_of_bits
    (Z.add
      (align (Zpos (XO (XO (XO (XO (XO XH))))))
        (Z.mul (alignof_composite' env ms) (Zpos (XO (XO (XO
          XH))))))
      (Z.mul
        (align (sizeof_variant' env ms)
          (alignof_composite' env ms)) (Zpos (XO (XO (XO
        XH))))))

(** val rank_type : composite_env0 -> type1 -> nat **)

let rank_type ce = function
| Tstruct0 (_, id) ->
  (match PTree.get id ce with
   | Some co -> S co.co_rank0
   | None -> O)
| Tvariant (_, id) ->
  (match PTree.get id ce with
   | Some co -> S co.co_rank0
   | None -> O)
| _ -> O

(** val rank_members : composite_env0 -> members0 -> nat **)

let rec rank_members ce = function
| Nil -> O
| Cons (m0, m1) ->
  let Member_plain0 (_, t0) = m0 in
  max (rank_type ce t0) (rank_members ce m1)

(** val sizeof_composite :
    composite_env0 -> struct_or_variant -> members0 -> z **)

let sizeof_composite env sv m =
  match sv with
  | Struct0 -> sizeof_struct env m
  | TaggedUnion -> sizeof_variant env m

(** val complete_members :
    composite_env0 -> members0 -> bool **)

let rec complete_members env = function
| Nil -> True
| Cons (m, ms0) ->
  (match complete_type env (type_member m) with
   | True -> complete_members env ms0
   | False -> False)

(** val composite_of_def :
    composite_env0 -> ident -> struct_or_variant -> members0
    -> origin list -> origin_rel list -> composite0 res **)

let composite_of_def env id su m orgs org_rels =
  match PTree.get id env with
  | Some _ ->
    Error (Cons ((MSG (String ((Ascii (True, False, True,
      True, False, False, True, False)), (String ((Ascii
      (True, False, True, False, True, True, True, False)),
      (String ((Ascii (False, False, True, True, False, True,
      True, False)), (String ((Ascii (False, False, True,
      False, True, True, True, False)), (String ((Ascii
      (True, False, False, True, False, True, True, False)),
      (String ((Ascii (False, False, False, False, True,
      True, True, False)), (String ((Ascii (False, False,
      True, True, False, True, True, False)), (String ((Ascii
      (True, False, True, False, False, True, True, False)),
      (String ((Ascii (False, False, False, False, False,
      True, False, False)), (String ((Ascii (False, False,
      True, False, False, True, True, False)), (String
      ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (False, True, True, False,
      False, True, True, False)), (String ((Ascii (True,
      False, False, True, False, True, True, False)), (String
      ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (True, False, False, True,
      False, True, True, False)), (String ((Ascii (False,
      False, True, False, True, True, True, False)), (String
      ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True,
      False, True, True, False)), (String ((Ascii (False,
      True, True, True, False, True, True, False)), (String
      ((Ascii (True, True, False, False, True, True, True,
      False)), (String ((Ascii (False, False, False, False,
      False, True, False, False)), (String ((Ascii (True,
      True, True, True, False, True, True, False)), (String
      ((Ascii (False, True, True, False, False, True, True,
      False)), (String ((Ascii (False, False, False, False,
      False, True, False, False)), (String ((Ascii (True,
      True, False, False, True, True, True, False)), (String
      ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (False, True, False, False,
      True, True, True, False)), (String ((Ascii (True,
      False, True, False, True, True, True, False)), (String
      ((Ascii (True, True, False, False, False, True, True,
      False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False,
      False, False, False, False, True, False, False)),
      (String ((Ascii (True, True, True, True, False, True,
      True, False)), (String ((Ascii (False, True, False,
      False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, False, True, False,
      False)), (String ((Ascii (False, True, True, False,
      True, True, True, False)), (String ((Ascii (True,
      False, False, False, False, True, True, False)),
      (String ((Ascii (False, True, False, False, True, True,
      True, False)), (String ((Ascii (True, False, False,
      True, False, True, True, False)), (String ((Ascii
      (True, False, False, False, False, True, True, False)),
      (String ((Ascii (False, True, True, True, False, True,
      True, False)), (String ((Ascii (False, False, True,
      False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, False, True, False,
      False)),
      EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      (Cons ((CTX id), Nil))))
  | None ->
    (match complete_members env m with
     | True ->
       let al = alignof_composite env su m in
       OK { co_generic_origins = orgs; co_origin_relations =
       org_rels; co_sv = su; co_members0 = m; co_sizeof0 =
       (align (sizeof_composite env su m) al); co_alignof0 =
       al; co_rank0 = (rank_members env m) }
     | False ->
       Error (Cons ((MSG (String ((Ascii (True, False, False,
         True, False, False, True, False)), (String ((Ascii
         (False, True, True, True, False, True, True,
         False)), (String ((Ascii (True, True, False, False,
         False, True, True, False)), (String ((Ascii (True,
         True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, True, False,
         True, True, False)), (String ((Ascii (False, False,
         False, False, True, True, True, False)), (String
         ((Ascii (False, False, True, True, False, True,
         True, False)), (String ((Ascii (True, False, True,
         False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, True, True, True,
         False)), (String ((Ascii (True, False, True, False,
         False, True, True, False)), (String ((Ascii (False,
         False, False, False, False, True, False, False)),
         (String ((Ascii (True, True, False, False, True,
         True, True, False)), (String ((Ascii (False, False,
         True, False, True, True, True, False)), (String
         ((Ascii (False, True, False, False, True, True,
         True, False)), (String ((Ascii (True, False, True,
         False, True, True, True, False)), (String ((Ascii
         (True, True, False, False, False, True, True,
         False)), (String ((Ascii (False, False, True, False,
         True, True, True, False)), (String ((Ascii (False,
         False, False, False, False, True, False, False)),
         (String ((Ascii (True, True, True, True, False,
         True, True, False)), (String ((Ascii (False, True,
         False, False, True, True, True, False)), (String
         ((Ascii (False, False, False, False, False, True,
         False, False)), (String ((Ascii (False, True, True,
         False, True, True, True, False)), (String ((Ascii
         (True, False, False, False, False, True, True,
         False)), (String ((Ascii (False, True, False, False,
         True, True, True, False)), (String ((Ascii (True,
         False, False, True, False, True, True, False)),
         (String ((Ascii (True, False, False, False, False,
         True, True, False)), (String ((Ascii (False, True,
         True, True, False, True, True, False)), (String
         ((Ascii (False, False, True, False, True, True,
         True, False)), (String ((Ascii (False, False, False,
         False, False, True, False, False)),
         EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Cons ((CTX id), Nil)))))

(** val add_composite_definitions :
    composite_env0 -> composite_definition0 list ->
    composite_env0 res **)

let rec add_composite_definitions env = function
| Nil -> OK env
| Cons (c, defs0) ->
  let Composite0 (id, su, m, orgs, org_rels) = c in
  bind (composite_of_def env id su m orgs org_rels)
    (fun co ->
    add_composite_definitions (PTree.set id co env) defs0)

(** val build_composite_env :
    composite_definition0 list -> composite_env0 res **)

let build_composite_env defs =
  add_composite_definitions PTree.empty defs

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

(** val typeof : expr -> type0 **)

let typeof = function
| Econst_int (_, ty) -> ty
| Econst_float (_, ty) -> ty
| Econst_single (_, ty) -> ty
| Econst_long (_, ty) -> ty
| Evar (_, ty) -> ty
| Etempvar (_, ty) -> ty
| Ederef (_, ty) -> ty
| Eaddrof (_, ty) -> ty
| Eunop (_, _, ty) -> ty
| Ebinop (_, _, _, ty) -> ty
| Ecast (_, ty) -> ty
| Efield (_, _, ty) -> ty
| Esizeof (_, ty) -> ty
| Ealignof (_, ty) -> ty

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

(** val to_rusttype : type0 -> type1 **)

let rec to_rusttype = function
| Tvoid0 -> Tunit
| Tint0 (sz, si, _) -> Tint1 (sz, si)
| Tlong0 (si, _) -> Tlong1 si
| Tfloat0 (fz, _) -> Tfloat1 fz
| Tpointer (ty0, _) ->
  Treference (XH, Mutable, (to_rusttype ty0))
| Tarray (ty', sz, _) -> Tarray0 ((to_rusttype ty'), sz)
| Tfunction (tyl, ty', cc) ->
  Tfunction0 (Nil, Nil, (to_rustlight tyl),
    (to_rusttype ty'), cc)
| Tstruct (id, _) -> Tstruct0 (Nil, id)
| Tunion (id, _) -> Tvariant (Nil, id)

(** val to_rustlight : typelist -> typelist0 **)

and to_rustlight = function
| Tnil -> Tnil0
| Tcons (ty, tyl0) ->
  Tcons0 ((to_rusttype ty), (to_rustlight tyl0))

(** val cexpr_to_place : expr -> place res **)

let rec cexpr_to_place = function
| Evar (id, ty) -> OK (Plocal (id, (to_rusttype ty)))
| Ederef (e', ty) ->
  bind (cexpr_to_place e') (fun p -> OK (Pderef (p,
    (to_rusttype ty))))
| Efield (e', id, ty) ->
  bind (cexpr_to_place e') (fun p -> OK (Pfield (p, id,
    (to_rusttype ty))))
| _ ->
  Error
    (msg (String ((Ascii (True, False, True, False, True,
      False, True, False)), (String ((Ascii (False, True,
      True, True, False, True, True, False)), (String ((Ascii
      (True, True, False, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, True, True,
      True, False)), (String ((Ascii (False, False, False,
      False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True,
      True, False)), (String ((Ascii (False, True, False,
      False, True, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, False, True,
      True, False)), (String ((Ascii (False, False, True,
      False, False, True, True, False)), (String ((Ascii
      (False, False, False, False, False, True, False,
      False)), (String ((Ascii (False, False, True, True,
      False, True, True, False)), (String ((Ascii (False,
      True, True, False, True, True, True, False)), (String
      ((Ascii (True, False, False, False, False, True, True,
      False)), (String ((Ascii (False, False, True, True,
      False, True, True, False)), (String ((Ascii (True,
      False, True, False, True, True, True, False)), (String
      ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (False, False, False, False,
      False, True, False, False)), (String ((Ascii (True,
      False, True, False, False, True, True, False)), (String
      ((Ascii (False, False, False, True, True, True, True,
      False)), (String ((Ascii (False, False, False, False,
      True, True, True, False)), (String ((Ascii (False,
      True, False, False, True, True, True, False)), (String
      ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, False, False,
      True, True, True, False)), (String ((Ascii (True, True,
      False, False, True, True, True, False)), (String
      ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True,
      False, True, True, False)), (String ((Ascii (False,
      True, True, True, False, True, True, False)),
      EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val cexpr_to_pexpr : expr -> pexpr res **)

let rec cexpr_to_pexpr = function
| Econst_int (i, ty) -> OK (Econst_int0 (i, (to_rusttype ty)))
| Econst_float (f, ty) ->
  OK (Econst_float0 (f, (to_rusttype ty)))
| Econst_single (f, ty) ->
  OK (Econst_single0 (f, (to_rusttype ty)))
| Econst_long (l, ty) ->
  OK (Econst_long0 (l, (to_rusttype ty)))
| Eaddrof (e0, ty) ->
  bind (cexpr_to_place e0) (fun p -> OK (Eref (XH, Mutable,
    p, (to_rusttype ty))))
| Eunop (op, e', ty) ->
  bind (cexpr_to_pexpr e') (fun pe -> OK (Eunop0 (op, pe,
    (to_rusttype ty))))
| Ebinop (op, e1, e2, ty) ->
  bind (cexpr_to_pexpr e1) (fun pe1 ->
    bind (cexpr_to_pexpr e2) (fun pe2 -> OK (Ebinop0 (op,
      pe1, pe2, (to_rusttype ty)))))
| _ ->
  Error
    (msg (String ((Ascii (True, False, True, False, True,
      False, True, False)), (String ((Ascii (False, True,
      True, True, False, True, True, False)), (String ((Ascii
      (True, True, False, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, True, True,
      True, False)), (String ((Ascii (False, False, False,
      False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True,
      True, False)), (String ((Ascii (False, True, False,
      False, True, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, False, True,
      True, False)), (String ((Ascii (False, False, True,
      False, False, True, True, False)), (String ((Ascii
      (False, False, False, False, False, True, False,
      False)), (String ((Ascii (False, True, False, False,
      True, True, True, False)), (String ((Ascii (False,
      True, True, False, True, True, True, False)), (String
      ((Ascii (True, False, False, False, False, True, True,
      False)), (String ((Ascii (False, False, True, True,
      False, True, True, False)), (String ((Ascii (True,
      False, True, False, True, True, True, False)), (String
      ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (False, False, False, False,
      False, True, False, False)), (String ((Ascii (True,
      False, True, False, False, True, True, False)), (String
      ((Ascii (False, False, False, True, True, True, True,
      False)), (String ((Ascii (False, False, False, False,
      True, True, True, False)), (String ((Ascii (False,
      True, False, False, True, True, True, False)), (String
      ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, False, False,
      True, True, True, False)), (String ((Ascii (True, True,
      False, False, True, True, True, False)), (String
      ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True,
      False, True, True, False)), (String ((Ascii (False,
      True, True, True, False, True, True, False)),
      EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val transl_expr_list : expr list -> pexpr list res **)

let rec transl_expr_list = function
| Nil -> OK Nil
| Cons (e, rest) ->
  bind (cexpr_to_pexpr e) (fun pe ->
    bind (transl_expr_list rest) (fun rest' -> OK (Cons (pe,
      rest'))))

(** val pexpr_to_expr : pexpr -> expr0 **)

let pexpr_to_expr pe =
  Epure pe

(** val empty_place : place **)

let empty_place =
  Plocal (XH, Tunit)

(** val transl_stmt : statement -> statement0 res **)

let rec transl_stmt = function
| Sskip -> OK Sskip0
| Sassign (e1, e2) ->
  bind (cexpr_to_place e1) (fun p ->
    bind (cexpr_to_pexpr e2) (fun pe -> OK (Sassign0 (p,
      (Epure pe)))))
| Scall (optid, e, args) ->
  bind (cexpr_to_pexpr e) (fun pe ->
    bind (transl_expr_list args) (fun pargs ->
      match optid with
      | Some id ->
        let ret_ty = to_rusttype (typeof e) in
        let place0 = Plocal (id, ret_ty) in
        OK (Scall0 (place0, (Epure pe),
        (map pexpr_to_expr pargs)))
      | None ->
        OK (Scall0 (empty_place, (Epure pe),
          (map pexpr_to_expr pargs)))))
| Ssequence (s1, s2) ->
  bind (transl_stmt s1) (fun rs1 ->
    bind (transl_stmt s2) (fun rs2 -> OK (Ssequence0 (rs1,
      rs2))))
| Sifthenelse (e, s1, s2) ->
  bind (cexpr_to_pexpr e) (fun pe ->
    bind (transl_stmt s1) (fun rs1 ->
      bind (transl_stmt s2) (fun rs2 -> OK (Sifthenelse0
        ((Epure pe), rs1, rs2)))))
| Sloop (s1, _) ->
  bind (transl_stmt s1) (fun rs1 -> OK (Sloop0 rs1))
| Sbreak -> OK Sbreak0
| Scontinue -> OK Scontinue0
| Sreturn o ->
  (match o with
   | Some e ->
     bind (cexpr_to_pexpr e) (fun pe ->
       let ret_place = Plocal ((XO XH),
         (to_rusttype (typeof e)))
       in
       OK (Ssequence0 ((Sassign0 (ret_place, (Epure pe))),
       (Sreturn0 ret_place))))
   | None -> OK (Sreturn0 empty_place))
| _ ->
  Error
    (msg (String ((Ascii (True, False, True, False, True,
      False, True, False)), (String ((Ascii (False, True,
      True, True, False, True, True, False)), (String ((Ascii
      (True, True, False, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, True, True,
      True, False)), (String ((Ascii (False, False, False,
      False, True, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True,
      True, False)), (String ((Ascii (False, True, False,
      False, True, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, False, True,
      True, False)), (String ((Ascii (False, False, True,
      False, False, True, True, False)), (String ((Ascii
      (False, False, False, False, False, True, False,
      False)), (String ((Ascii (True, True, False, False,
      True, True, True, False)), (String ((Ascii (False,
      False, True, False, True, True, True, False)), (String
      ((Ascii (True, False, False, False, False, True, True,
      False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (True,
      False, True, False, False, True, True, False)), (String
      ((Ascii (True, False, True, True, False, True, True,
      False)), (String ((Ascii (True, False, True, False,
      False, True, True, False)), (String ((Ascii (False,
      True, True, True, False, True, True, False)), (String
      ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (False, False, False, False,
      False, True, False, False)), (String ((Ascii (False,
      False, True, False, True, True, True, False)), (String
      ((Ascii (True, False, False, True, True, True, True,
      False)), (String ((Ascii (False, False, False, False,
      True, True, True, False)), (String ((Ascii (True,
      False, True, False, False, True, True, False)),
      EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val transl_function : function0 -> function1 res **)

let transl_function f =
  bind (transl_stmt f.fn_body) (fun body -> OK
    { fn_generic_origins = Nil; fn_origins_relation = Nil;
    fn_drop_glue = None; fn_return0 =
    (to_rusttype f.fn_return); fn_callconv0 = f.fn_callconv;
    fn_vars0 =
    (map (fun pat ->
      let Pair (id, ty) = pat in Pair (id, (to_rusttype ty)))
      (app f.fn_vars f.fn_temps)); fn_params0 =
    (map (fun pat ->
      let Pair (id, ty) = pat in Pair (id, (to_rusttype ty)))
      f.fn_params); fn_body0 = body })

(** val transl_fundef : ident -> fundef1 -> fundef2 res **)

let transl_fundef _ = function
| Internal func ->
  bind (transl_function func) (fun tf -> OK (Internal0 tf))
| External (extfun, typelist1, ty, cconv) ->
  OK (External0 (Nil, Nil, extfun, (to_rustlight typelist1),
    (to_rusttype ty), cconv))

(** val transl_globvar : ident -> type0 -> type1 res **)

let transl_globvar _ ty =
  OK (to_rusttype ty)

(** val convert_members : members -> members0 res **)

let rec convert_members = function
| Nil -> OK Nil
| Cons (h, t0) ->
  (match h with
   | Member_plain (id, ty) ->
     bind (convert_members t0) (fun cm -> OK (Cons
       ((Member_plain0 (id, (to_rusttype ty))), cm)))
   | Member_bitfield (_, _, _, _, _, _) ->
     Error
       (msg (String ((Ascii (False, True, True, True, False,
         True, True, False)), (String ((Ascii (True, True,
         True, True, False, True, True, False)), (String
         ((Ascii (False, False, True, False, True, True,
         True, False)), (String ((Ascii (False, False, False,
         False, False, True, False, False)), (String ((Ascii
         (True, True, False, False, True, True, True,
         False)), (String ((Ascii (True, False, True, False,
         True, True, True, False)), (String ((Ascii (False,
         False, False, False, True, True, True, False)),
         (String ((Ascii (False, False, False, False, True,
         True, True, False)), (String ((Ascii (True, True,
         True, True, False, True, True, False)), (String
         ((Ascii (False, True, False, False, True, True,
         True, False)), (String ((Ascii (False, False, True,
         False, True, True, True, False)), (String ((Ascii
         (False, False, False, False, False, True, False,
         False)), (String ((Ascii (True, False, True, True,
         False, True, True, False)), (String ((Ascii (True,
         False, True, False, False, True, True, False)),
         (String ((Ascii (True, False, True, True, False,
         True, True, False)), (String ((Ascii (False, True,
         False, False, False, True, True, False)), (String
         ((Ascii (True, False, True, False, False, True,
         True, False)), (String ((Ascii (False, True, False,
         False, True, True, True, False)), (String ((Ascii
         (False, False, False, False, False, True, False,
         False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (True,
         False, False, True, False, True, True, False)),
         (String ((Ascii (False, False, True, False, True,
         True, True, False)), (String ((Ascii (False, True,
         True, False, False, True, True, False)), (String
         ((Ascii (True, False, False, True, False, True,
         True, False)), (String ((Ascii (True, False, True,
         False, False, True, True, False)), (String ((Ascii
         (False, False, True, True, False, True, True,
         False)), (String ((Ascii (False, False, True, False,
         False, True, True, False)),
         EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val convert_composite_definition :
    composite_definition list -> composite_definition0 list
    res **)

let rec convert_composite_definition = function
| Nil -> OK Nil
| Cons (c, t0) ->
  let Composite (id, su, m, _) = c in
  let new_su =
    match su with
    | Struct -> Struct0
    | Union -> TaggedUnion
  in
  bind (convert_members m) (fun new_m ->
    bind (convert_composite_definition t0) (fun rcd -> OK
      (Cons ((Composite0 (id, new_su, new_m, Nil, Nil)),
      rcd))))

(** val transl_program : program2 -> program3 res **)

let transl_program p =
  match convert_composite_definition p.prog_types with
  | OK co_defs ->
    let tce = build_composite_env co_defs in
    (match tce with
     | OK tce0 ->
       bind
         (transform_partial_program2 transl_fundef
           transl_globvar (program_of_program p)) (fun p1 ->
         OK { prog_defs1 = p1.prog_defs; prog_public1 =
         p1.prog_public; prog_main1 = p1.prog_main;
         prog_types0 = co_defs; prog_comp_env0 = tce0 })
     | Error msg0 -> Error msg0)
  | Error _ ->
    Error
      (msg (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (False, True,
        False, False, True, True, True, False)), (String
        ((Ascii (False, True, False, False, True, True, True,
        False)), (String ((Ascii (True, True, True, True,
        False, True, True, False)), (String ((Ascii (False,
        True, False, False, True, True, True, False)),
        (String ((Ascii (False, False, False, False, False,
        True, False, False)), (String ((Ascii (True, False,
        False, True, False, True, True, False)), (String
        ((Ascii (False, True, True, True, False, True, True,
        False)), (String ((Ascii (False, False, False, False,
        False, True, False, False)), (String ((Ascii (False,
        False, True, False, True, True, True, False)),
        (String ((Ascii (False, True, False, False, True,
        True, True, False)), (String ((Ascii (True, False,
        False, False, False, True, True, False)), (String
        ((Ascii (False, True, True, True, False, True, True,
        False)), (String ((Ascii (True, True, False, False,
        True, True, True, False)), (String ((Ascii (False,
        False, True, True, False, True, True, False)),
        (String ((Ascii (True, True, True, True, True, False,
        True, False)), (String ((Ascii (True, True, False,
        False, False, True, True, False)), (String ((Ascii
        (True, True, True, True, False, True, True, False)),
        (String ((Ascii (True, False, True, True, False,
        True, True, False)), (String ((Ascii (False, False,
        False, False, True, True, True, False)), (String
        ((Ascii (True, True, True, True, False, True, True,
        False)), (String ((Ascii (True, True, False, False,
        True, True, True, False)), (String ((Ascii (True,
        False, False, True, False, True, True, False)),
        (String ((Ascii (False, False, True, False, True,
        True, True, False)), (String ((Ascii (True, False,
        True, False, False, True, True, False)), (String
        ((Ascii (True, True, False, False, True, True, True,
        False)), (String ((Ascii (False, False, False, False,
        False, True, False, False)), (String ((Ascii (False,
        False, False, True, False, True, False, False)),
        (String ((Ascii (True, True, False, False, False,
        True, True, False)), (String ((Ascii (False, False,
        True, True, False, True, True, False)), (String
        ((Ascii (True, False, False, True, False, True, True,
        False)), (String ((Ascii (True, True, True, False,
        False, True, True, False)), (String ((Ascii (False,
        False, False, True, False, True, True, False)),
        (String ((Ascii (False, False, True, False, True,
        True, True, False)), (String ((Ascii (False, True,
        False, False, True, True, False, False)), (String
        ((Ascii (False, True, False, False, True, True, True,
        False)), (String ((Ascii (True, False, True, False,
        True, True, True, False)), (String ((Ascii (True,
        True, False, False, True, True, True, False)),
        (String ((Ascii (False, False, True, False, True,
        True, True, False)), (String ((Ascii (False, False,
        True, True, False, True, True, False)), (String
        ((Ascii (True, False, False, True, False, True, True,
        False)), (String ((Ascii (True, True, True, False,
        False, True, True, False)), (String ((Ascii (False,
        False, False, True, False, True, True, False)),
        (String ((Ascii (False, False, True, False, True,
        True, True, False)), (String ((Ascii (True, False,
        False, True, False, True, False, False)),
        EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
