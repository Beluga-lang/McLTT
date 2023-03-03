
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val implb : bool -> bool -> bool **)

let implb b1 b2 =
  if b1 then b2 else true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



(** val add : int -> int -> int **)

let rec add = (+)



module type EqLtLe =
 sig
  type t
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    let c = compSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> true
     | _ -> false)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module Nat =
 struct
  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt
 end

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
    | XH -> (match y with
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

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

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

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> false)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> false)
    | XH -> (match x0 with
             | XH -> true
             | _ -> false)
 end

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a :: l0 -> rev_append l0 (a :: l')

(** val rev' : 'a1 list -> 'a1 list **)

let rev' l =
  rev_append l []

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t0 -> fold_left f t0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t0 -> f b (fold_right f a0 t0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

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
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
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
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

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
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos p0 -> Pos.eq_dec p p0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg p0 -> Pos.eq_dec p p0
                 | _ -> false)
 end

type 'x compare0 =
| LT
| EQ
| GT

module type Coq_OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module Coq_OrderedTypeFacts =
 functor (O:Coq_OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:Coq_OrderedType) ->
 struct
  module MO = Coq_OrderedTypeFacts(O)
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = z

  (** val _0 : z **)

  let _0 =
    Z0

  (** val _1 : z **)

  let _1 =
    Zpos XH

  (** val _2 : z **)

  let _2 =
    Zpos (XO XH)

  (** val _3 : z **)

  let _3 =
    Zpos (XI XH)

  (** val add : z -> z -> z **)

  let add =
    Z.add

  (** val opp : z -> z **)

  let opp =
    Z.opp

  (** val sub : z -> z -> z **)

  let sub =
    Z.sub

  (** val mul : z -> z -> z **)

  let mul =
    Z.mul

  (** val max : z -> z -> z **)

  let max =
    Z.max

  (** val eqb : z -> z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : z -> z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : z -> z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : z -> z -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : z -> z -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : z -> z -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> z **)

  let i2z n0 =
    n0
 end

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module MakeRaw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type elt = X.t

  type tree =
  | Leaf
  | Node of I.t * tree * X.t * tree

  (** val empty : tree **)

  let empty =
    Leaf

  (** val is_empty : tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _) -> false

  (** val mem : X.t -> tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (_, l, k, r) ->
    (match X.compare x k with
     | Eq -> true
     | Lt -> mem x l
     | Gt -> mem x r)

  (** val min_elt : tree -> elt option **)

  let rec min_elt = function
  | Leaf -> None
  | Node (_, l, x, _) ->
    (match l with
     | Leaf -> Some x
     | Node (_, _, _, _) -> min_elt l)

  (** val max_elt : tree -> elt option **)

  let rec max_elt = function
  | Leaf -> None
  | Node (_, _, x, r) ->
    (match r with
     | Leaf -> Some x
     | Node (_, _, _, _) -> max_elt r)

  (** val choose : tree -> elt option **)

  let choose =
    min_elt

  (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

  let rec fold f t0 base =
    match t0 with
    | Leaf -> base
    | Node (_, l, x, r) -> fold f r (f x (fold f l base))

  (** val elements_aux : X.t list -> tree -> X.t list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (_, l, x, r) -> elements_aux (x :: (elements_aux acc r)) l

  (** val elements : tree -> X.t list **)

  let elements =
    elements_aux []

  (** val rev_elements_aux : X.t list -> tree -> X.t list **)

  let rec rev_elements_aux acc = function
  | Leaf -> acc
  | Node (_, l, x, r) -> rev_elements_aux (x :: (rev_elements_aux acc l)) r

  (** val rev_elements : tree -> X.t list **)

  let rev_elements =
    rev_elements_aux []

  (** val cardinal : tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (_, l, _, r) -> Stdlib.Int.succ (add (cardinal l) (cardinal r))

  (** val maxdepth : tree -> int **)

  let rec maxdepth = function
  | Leaf -> 0
  | Node (_, l, _, r) ->
    Stdlib.Int.succ (Stdlib.max (maxdepth l) (maxdepth r))

  (** val mindepth : tree -> int **)

  let rec mindepth = function
  | Leaf -> 0
  | Node (_, l, _, r) ->
    Stdlib.Int.succ (Stdlib.min (mindepth l) (mindepth r))

  (** val for_all : (elt -> bool) -> tree -> bool **)

  let rec for_all f = function
  | Leaf -> true
  | Node (_, l, x, r) ->
    if if f x then for_all f l else false then for_all f r else false

  (** val exists_ : (elt -> bool) -> tree -> bool **)

  let rec exists_ f = function
  | Leaf -> false
  | Node (_, l, x, r) ->
    if if f x then true else exists_ f l then true else exists_ f r

  type enumeration =
  | End
  | More of elt * tree * enumeration

  (** val cons : tree -> enumeration -> enumeration **)

  let rec cons s e =
    match s with
    | Leaf -> e
    | Node (_, l, x, r) -> cons l (More (x, r, e))

  (** val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison **)

  let compare_more x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match X.compare x1 x2 with
     | Eq -> cont (cons r2 e3)
     | x -> x)

  (** val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison **)

  let rec compare_cont s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (_, l1, x1, r1) ->
      compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

  (** val compare_end : enumeration -> comparison **)

  let compare_end = function
  | End -> Eq
  | More (_, _, _) -> Lt

  (** val compare : tree -> tree -> comparison **)

  let compare s1 s2 =
    compare_cont s1 compare_end (cons s2 End)

  (** val equal : tree -> tree -> bool **)

  let equal s1 s2 =
    match compare s1 s2 with
    | Eq -> true
    | _ -> false

  (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)

  let rec subsetl subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (_, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl subset_l1 x1 l2
     | Gt -> if mem x1 r2 then subset_l1 s2 else false)

  (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)

  let rec subsetr subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (_, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr subset_r1 x1 r2)

  (** val subset : tree -> tree -> bool **)

  let rec subset s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> false
       | Node (_, l2, x2, r2) ->
         (match X.compare x1 x2 with
          | Eq -> if subset l1 l2 then subset r1 r2 else false
          | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
          | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))

  type t = tree

  (** val height : t -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (h, _, _, _) -> h

  (** val singleton : X.t -> tree **)

  let singleton x =
    Node (I._1, Leaf, x, Leaf)

  (** val create : t -> X.t -> t -> tree **)

  let create l x r =
    Node ((I.add (I.max (height l) (height r)) I._1), l, x, r)

  (** val assert_false : t -> X.t -> t -> tree **)

  let assert_false =
    create

  (** val bal : t -> X.t -> t -> tree **)

  let bal l x r =
    let hl = height l in
    let hr = height r in
    if I.ltb (I.add hr I._2) hl
    then (match l with
          | Leaf -> assert_false l x r
          | Node (_, ll, lx, lr) ->
            if I.leb (height lr) (height ll)
            then create ll lx (create lr x r)
            else (match lr with
                  | Leaf -> assert_false l x r
                  | Node (_, lrl, lrx, lrr) ->
                    create (create ll lx lrl) lrx (create lrr x r)))
    else if I.ltb (I.add hl I._2) hr
         then (match r with
               | Leaf -> assert_false l x r
               | Node (_, rl, rx, rr) ->
                 if I.leb (height rl) (height rr)
                 then create (create l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false l x r
                       | Node (_, rll, rlx, rlr) ->
                         create (create l x rll) rlx (create rlr rx rr)))
         else create l x r

  (** val add : X.t -> tree -> tree **)

  let rec add x = function
  | Leaf -> Node (I._1, Leaf, x, Leaf)
  | Node (h, l, y, r) ->
    (match X.compare x y with
     | Eq -> Node (h, l, y, r)
     | Lt -> bal (add x l) y r
     | Gt -> bal l y (add x r))

  (** val join : tree -> elt -> t -> t **)

  let rec join l = match l with
  | Leaf -> add
  | Node (lh, ll, lx, lr) ->
    (fun x ->
      let rec join_aux r = match r with
      | Leaf -> add x l
      | Node (rh, rl, rx, rr) ->
        if I.ltb (I.add rh I._2) lh
        then bal ll lx (join lr x r)
        else if I.ltb (I.add lh I._2) rh
             then bal (join_aux rl) rx rr
             else create l x r
      in join_aux)

  (** val remove_min : tree -> elt -> t -> t * elt **)

  let rec remove_min l x r =
    match l with
    | Leaf -> (r, x)
    | Node (_, ll, lx, lr) ->
      let (l', m) = remove_min ll lx lr in ((bal l' x r), m)

  (** val merge : tree -> tree -> tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, l2, x2, r2) ->
         let (s2', m) = remove_min l2 x2 r2 in bal s1 m s2')

  (** val remove : X.t -> tree -> tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Eq -> merge l r
     | Lt -> bal (remove x l) y r
     | Gt -> bal l y (remove x r))

  (** val concat : tree -> tree -> tree **)

  let concat s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, l2, x2, r2) ->
         let (s2', m) = remove_min l2 x2 r2 in join s1 m s2')

  type triple = { t_left : t; t_in : bool; t_right : t }

  (** val t_left : triple -> t **)

  let t_left t0 =
    t0.t_left

  (** val t_in : triple -> bool **)

  let t_in t0 =
    t0.t_in

  (** val t_right : triple -> t **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> tree -> triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b; t_right = rl } = split x l in
       { t_left = ll; t_in = b; t_right = (join rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b; t_right = rr } = split x r in
       { t_left = (join l y rl); t_in = b; t_right = rr })

  (** val inter : tree -> tree -> tree **)

  let rec inter s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then join (inter l1 l2') x1 (inter r1 r2')
         else concat (inter l1 l2') (inter r1 r2'))

  (** val diff : tree -> tree -> tree **)

  let rec diff s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then concat (diff l1 l2') (diff r1 r2')
         else join (diff l1 l2') x1 (diff r1 r2'))

  (** val union : tree -> tree -> tree **)

  let rec union s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = _; t_right = r2' } = split x1 s2 in
         join (union l1 l2') x1 (union r1 r2'))

  (** val filter : (elt -> bool) -> tree -> tree **)

  let rec filter f = function
  | Leaf -> Leaf
  | Node (_, l, x, r) ->
    let l' = filter f l in
    let r' = filter f r in if f x then join l' x r' else concat l' r'

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f = function
  | Leaf -> (Leaf, Leaf)
  | Node (_, l, x, r) ->
    let (l1, l2) = partition f l in
    let (r1, r2) = partition f r in
    if f x
    then ((join l1 x r1), (concat l2 r2))
    else ((concat l1 r1), (join l2 x r2))

  (** val ltb_tree : X.t -> tree -> bool **)

  let rec ltb_tree x = function
  | Leaf -> true
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Gt -> (&&) (ltb_tree x l) (ltb_tree x r)
     | _ -> false)

  (** val gtb_tree : X.t -> tree -> bool **)

  let rec gtb_tree x = function
  | Leaf -> true
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Lt -> (&&) (gtb_tree x l) (gtb_tree x r)
     | _ -> false)

  (** val isok : tree -> bool **)

  let rec isok = function
  | Leaf -> true
  | Node (_, l, x, r) ->
    (&&) ((&&) ((&&) (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)

  module MX = OrderedTypeFacts(X)

  type coq_R_min_elt =
  | R_min_elt_0 of tree
  | R_min_elt_1 of tree * I.t * tree * X.t * tree
  | R_min_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
     tree * elt option * coq_R_min_elt

  type coq_R_max_elt =
  | R_max_elt_0 of tree
  | R_max_elt_1 of tree * I.t * tree * X.t * tree
  | R_max_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
     tree * elt option * coq_R_max_elt

  module L = MakeListOrdering(X)

  (** val flatten_e : enumeration -> elt list **)

  let rec flatten_e = function
  | End -> []
  | More (x, t0, r) -> x :: (app (elements t0) (flatten_e r))

  type coq_R_bal =
  | R_bal_0 of t * X.t * t
  | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t * tree
  | R_bal_4 of t * X.t * t
  | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t * tree
  | R_bal_8 of t * X.t * t

  type coq_R_remove_min =
  | R_remove_min_0 of tree * elt * t
  | R_remove_min_1 of tree * elt * t * I.t * tree * X.t * tree * (t * elt)
     * coq_R_remove_min * t * elt

  type coq_R_merge =
  | R_merge_0 of tree * tree
  | R_merge_1 of tree * tree * I.t * tree * X.t * tree
  | R_merge_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * elt

  type coq_R_concat =
  | R_concat_0 of tree * tree
  | R_concat_1 of tree * tree * I.t * tree * X.t * tree
  | R_concat_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * elt

  type coq_R_inter =
  | R_inter_0 of tree * tree
  | R_inter_1 of tree * tree * I.t * tree * X.t * tree
  | R_inter_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  | R_inter_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter

  type coq_R_diff =
  | R_diff_0 of tree * tree
  | R_diff_1 of tree * tree * I.t * tree * X.t * tree
  | R_diff_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  | R_diff_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff

  type coq_R_union =
  | R_union_0 of tree * tree
  | R_union_1 of tree * tree * I.t * tree * X.t * tree
  | R_union_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_union * tree * coq_R_union
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module Raw = MakeRaw(I)(X)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> int **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f (this s) in ((fst p), (snd p))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)
 end

module type OrderedTypeOrig =
 Coq_OrderedType

module Update_OT =
 functor (O:OrderedTypeOrig) ->
 struct
  type t = O.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val compare : O.t -> O.t -> comparison **)

  let compare x y =
    match O.compare x y with
    | LT -> Lt
    | EQ -> Eq
    | GT -> Gt
 end

module Coq_IntMake =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  module X' = Update_OT(X)

  module MSet = IntMake(I)(X')

  type elt = X.t

  type t = MSet.t

  (** val empty : t **)

  let empty =
    MSet.empty

  (** val is_empty : t -> bool **)

  let is_empty =
    MSet.is_empty

  (** val mem : elt -> t -> bool **)

  let mem =
    MSet.mem

  (** val add : elt -> t -> t **)

  let add =
    MSet.add

  (** val singleton : elt -> t **)

  let singleton =
    MSet.singleton

  (** val remove : elt -> t -> t **)

  let remove =
    MSet.remove

  (** val union : t -> t -> t **)

  let union =
    MSet.union

  (** val inter : t -> t -> t **)

  let inter =
    MSet.inter

  (** val diff : t -> t -> t **)

  let diff =
    MSet.diff

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    MSet.eq_dec

  (** val equal : t -> t -> bool **)

  let equal =
    MSet.equal

  (** val subset : t -> t -> bool **)

  let subset =
    MSet.subset

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold =
    MSet.fold

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all =
    MSet.for_all

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ =
    MSet.exists_

  (** val filter : (elt -> bool) -> t -> t **)

  let filter =
    MSet.filter

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition =
    MSet.partition

  (** val cardinal : t -> int **)

  let cardinal =
    MSet.cardinal

  (** val elements : t -> elt list **)

  let elements =
    MSet.elements

  (** val choose : t -> elt option **)

  let choose =
    MSet.choose

  module MF =
   struct
    (** val eqb : X.t -> X.t -> bool **)

    let eqb x y =
      if MSet.E.eq_dec x y then true else false
   end

  (** val min_elt : t -> elt option **)

  let min_elt =
    MSet.min_elt

  (** val max_elt : t -> elt option **)

  let max_elt =
    MSet.max_elt

  (** val compare : t -> t -> t compare0 **)

  let compare s s' =
    let c = compSpec2Type s s' (MSet.compare s s') in
    (match c with
     | CompEqT -> EQ
     | CompLtT -> LT
     | CompGtT -> GT)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> t compare0 **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end
 end

module Make =
 functor (X:Coq_OrderedType) ->
 Coq_IntMake(Z_as_Int)(X)

module Raw =
 functor (X:Coq_OrderedType) ->
 struct
  module MX = Coq_OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 f2 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f f0 f1 f2 s =
    let f3 = f s in
    let f4 = f0 s in
    let f5 = f1 s in
    let f6 = f2 s in
    (match s with
     | [] -> f3 __
     | a :: l ->
       let (a0, b) = a in
       let f7 = f6 a0 b l __ in
       let f8 = fun _ _ -> let hrec = mem_rect k f f0 f1 f2 l in f7 __ __ hrec
       in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match X.compare k a0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_3 (y, y0, y1, y2, (mem k y2),
      (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 f2 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 f2 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f f0 f1 f2 s =
    let f3 = f s in
    let f4 = f0 s in
    let f5 = f1 s in
    let f6 = f2 s in
    (match s with
     | [] -> f3 __
     | a :: l ->
       let (a0, b) = a in
       let f7 = f6 a0 b l __ in
       let f8 = fun _ _ ->
         let hrec = find_rect k f f0 f1 f2 l in f7 __ __ hrec
       in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match X.compare k a0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_3 (y, y0, y1, y2, (find k y2),
      (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rect k x f f0 f1 f2 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rec k x f f0 f1 f2 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x f f0 f1 f2 s =
    let f3 = f s in
    let f4 = f0 s in
    let f5 = f1 s in
    let f6 = f2 s in
    (match s with
     | [] -> f3 __
     | a :: l ->
       let (a0, b) = a in
       let f7 = f6 a0 b l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x f f0 f1 f2 l in f7 __ __ hrec
       in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match X.compare k a0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x s _res =
    add_rect k x (fun y _ _ _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ _ _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ _ _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_3 (y, y0, y1, y2,
      (add k x y2), (y6 (add k x y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 f2 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f f0 f1 f2 s =
    let f3 = f s in
    let f4 = f0 s in
    let f5 = f1 s in
    let f6 = f2 s in
    (match s with
     | [] -> f3 __
     | a :: l ->
       let (a0, b) = a in
       let f7 = f6 a0 b l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f f0 f1 f2 l in f7 __ __ hrec
       in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match X.compare k a0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_3 (y, y0, y1, y2,
      (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let rec fold_rect f f0 f1 m acc =
    let f2 = f0 m acc in
    let f3 = f1 m acc in
    (match m with
     | [] -> f2 __
     | a :: l ->
       let (a0, b) = a in
       let f4 = f3 a0 b l __ in
       let hrec = fold_rect f f0 f1 l (f a0 b acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2, y3,
      (fold f y3 (f y1 y2 y0)), (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res
      __

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp e e') (equal cmp l l')
          | _ -> false))

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rect cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rec cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let rec equal_rect cmp f f0 f1 f2 m m' =
    let f3 = f m m' in
    let f4 = f0 m m' in
    let f5 = f1 m m' in
    let f6 = f2 m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | [] -> let f9 = f3 __ in (match m' with
                                | [] -> f9 __
                                | _ :: _ -> f8 __)
     | a :: l ->
       let (a0, b) = a in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match m' with
        | [] -> f8 __
        | a1 :: l0 ->
          let (a2, b0) = a1 in
          let f11 = f9 a2 b0 l0 __ in
          let f12 = let _x = X.compare a0 a2 in f11 _x __ in
          let f13 = f10 a2 b0 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f f0 f1 f2 l l0 in f13 __ __ hrec
          in
          (match X.compare a0 a2 with
           | EQ -> f14 __ __
           | _ -> f12 __)))

  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let equal_rec =
    equal_rect

  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)

  let coq_R_equal_correct cmp m m' _res =
    equal_rect cmp (fun y y0 _ _ _ _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal cmp y3 y7), (y11 (equal cmp y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ _ _ -> R_equal_3 (y, y0, y1,
      y3)) m m' _res __

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rect f f0 t1) k y t2 (tree_rect f f0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rec f f0 t1) k y t2 (tree_rec f f0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (l, _, _, r, _) -> Stdlib.Int.succ (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> (r, (x, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) -> elements_aux ((x, d) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = Coq_OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (l, x, d, r) -> f l x d r __ __ __
    | R_bal_1 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_2 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_3 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_4 (l, x, d, r) -> f3 l x d r __ __ __ __ __
    | R_bal_5 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_6 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_7 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_8 (l, x, d, r) -> f7 l x d r __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (l, x, d, r) -> f l x d r __ __ __
    | R_bal_1 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_2 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_3 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_4 (l, x, d, r) -> f3 l x d r __ __ __ __ __
    | R_bal_5 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_6 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_7 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_8 (l, x, d, r) -> f7 l x d r __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r) -> f l x d r __
    | R_remove_min_1 (l, x, d, r, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r) -> f l x d r __
    | R_remove_min_1 (l, x, d, r, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (s1, s2) -> f s1 s2 __
    | R_merge_1 (s1, s2, _x, _x0, _x1, _x2, _x3) ->
      f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __
    | R_merge_2 (s1, s2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, s2', p,
                 x, d) ->
      f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (s1, s2) -> f s1 s2 __
    | R_merge_1 (s1, s2, _x, _x0, _x1, _x2, _x3) ->
      f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __
    | R_merge_2 (s1, s2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, s2', p,
                 x, d) ->
      f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (m1, m2) -> f m1 m2 __
    | R_concat_1 (m1, m2, _x, _x0, _x1, _x2, _x3) ->
      f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __
    | R_concat_2 (m1, m2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, m2', xd) ->
      f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (m1, m2) -> f m1 m2 __
    | R_concat_1 (m1, m2, _x, _x0, _x1, _x2, _x3) ->
      f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __
    | R_concat_2 (m1, m2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, m2', xd) ->
      f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t0, r) -> (x, e0) :: (app (elements t0) (flatten_e r))
   end
 end

module Coq0_IntMake =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> int **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Coq_Make =
 functor (X:Coq_OrderedType) ->
 Coq0_IntMake(Z_as_Int)(X)

type 'a comparable =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_Comparable *)

(** val compare1 : 'a1 comparable -> 'a1 -> 'a1 -> comparison **)

let compare1 comparable0 =
  comparable0

(** val natComparable : int comparable **)

let natComparable =
  Nat.compare

(** val pairComparable :
    'a1 comparable -> 'a2 comparable -> ('a1 * 'a2) comparable **)

let pairComparable cA cB x y =
  let (xa, xb) = x in
  let (ya, yb) = y in
  (match compare1 cA xa ya with
   | Eq -> compare1 cB xb yb
   | x0 -> x0)

(** val compare_eqb : 'a1 comparable -> 'a1 -> 'a1 -> bool **)

let compare_eqb c x y =
  match compare1 c x y with
  | Eq -> true
  | _ -> false

type 'a finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

(** val all_list : 'a1 finite -> 'a1 list **)

let all_list finite0 =
  finite0

type 'a alphabet = { alphabetComparable : 'a comparable;
                     alphabetFinite : 'a finite }

type 'a numbered = { inj : ('a -> positive); surj : (positive -> 'a);
                     inj_bound : positive }

(** val numberedAlphabet : 'a1 numbered -> 'a1 alphabet **)

let numberedAlphabet n0 =
  { alphabetComparable = (fun x y -> Pos.compare (n0.inj x) (n0.inj y));
    alphabetFinite =
    (fst
      (Pos.iter (fun pat ->
        let (l, p) = pat in (((n0.surj p) :: l), (Pos.succ p))) ([], XH)
        n0.inj_bound)) }

module type ComparableM =
 sig
  type t

  val tComparable : t comparable
 end

module OrderedTypeAlt_from_ComparableM =
 functor (C:ComparableM) ->
 struct
  type t = C.t

  (** val compare : t -> t -> comparison **)

  let compare =
    compare1 C.tComparable
 end

module OrderedType_from_ComparableM =
 functor (C:ComparableM) ->
 struct
  module Alt = OrderedTypeAlt_from_ComparableM(C)

  type t = Alt.t

  (** val compare : Alt.t -> Alt.t -> Alt.t compare0 **)

  let compare x y =
    match Alt.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : Alt.t -> Alt.t -> bool **)

  let eq_dec x y =
    match Alt.compare x y with
    | Eq -> true
    | _ -> false
 end

type 'x arrows_right = __

module type T =
 sig
  type terminal

  type nonterminal

  val coq_TerminalAlph : terminal alphabet

  val coq_NonTerminalAlph : nonterminal alphabet

  type symbol =
  | T of terminal
  | NT of nonterminal

  val symbol_rect : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

  val symbol_rec : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

  val coq_SymbolAlph : symbol alphabet

  type symbol_semantic_type

  type production

  val coq_ProductionAlph : production alphabet

  val prod_lhs : production -> nonterminal

  val prod_rhs_rev : production -> symbol list

  val prod_action : production -> symbol_semantic_type arrows_right

  type token

  val token_term : token -> terminal

  val token_sem : token -> symbol_semantic_type
 end

module type Coq_T =
 sig
  module Gram :
   T

  type noninitstate

  val coq_NonInitStateAlph : noninitstate alphabet

  type initstate

  val coq_InitStateAlph : initstate alphabet

  val last_symb_of_non_init_state : noninitstate -> Gram.symbol

  type state =
  | Init of initstate
  | Ninit of noninitstate

  val state_rect : (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1

  val state_rec : (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1

  val coq_StateAlph : state alphabet

  type lookahead_action =
  | Shift_act of noninitstate
  | Reduce_act of Gram.production
  | Fail_act

  val lookahead_action_rect :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> lookahead_action -> 'a1

  val lookahead_action_rec :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> lookahead_action -> 'a1

  type action =
  | Default_reduce_act of Gram.production
  | Lookahead_act of (Gram.terminal -> lookahead_action)

  val action_rect :
    (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) -> 'a1)
    -> action -> 'a1

  val action_rec :
    (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) -> 'a1)
    -> action -> 'a1

  type item = { prod_item : Gram.production; dot_pos_item : int;
                lookaheads_item : Gram.terminal list }

  val prod_item : item -> Gram.production

  val dot_pos_item : item -> int

  val lookaheads_item : item -> Gram.terminal list

  module GramDefs :
   sig
    type parse_tree =
    | Terminal_pt of Gram.token
    | Non_terminal_pt of Gram.production * Gram.token list * parse_tree_list
    and parse_tree_list =
    | Nil_ptl
    | Cons_ptl of Gram.symbol list * Gram.token list * parse_tree_list
       * Gram.symbol * Gram.token list * parse_tree

    val parse_tree_rect :
      (Gram.token -> 'a1) -> (Gram.production -> Gram.token list ->
      parse_tree_list -> 'a1) -> Gram.symbol -> Gram.token list -> parse_tree
      -> 'a1

    val parse_tree_rec :
      (Gram.token -> 'a1) -> (Gram.production -> Gram.token list ->
      parse_tree_list -> 'a1) -> Gram.symbol -> Gram.token list -> parse_tree
      -> 'a1

    val parse_tree_list_rect :
      'a1 -> (Gram.symbol list -> Gram.token list -> parse_tree_list -> 'a1
      -> Gram.symbol -> Gram.token list -> parse_tree -> 'a1) -> Gram.symbol
      list -> Gram.token list -> parse_tree_list -> 'a1

    val parse_tree_list_rec :
      'a1 -> (Gram.symbol list -> Gram.token list -> parse_tree_list -> 'a1
      -> Gram.symbol -> Gram.token list -> parse_tree -> 'a1) -> Gram.symbol
      list -> Gram.token list -> parse_tree_list -> 'a1

    val pt_sem :
      Gram.symbol -> Gram.token list -> parse_tree ->
      Gram.symbol_semantic_type

    val ptl_sem :
      Gram.symbol list -> Gram.token list -> parse_tree_list -> 'a1
      arrows_right -> 'a1

    val pt_size : Gram.symbol -> Gram.token list -> parse_tree -> int

    val ptl_size :
      Gram.symbol list -> Gram.token list -> parse_tree_list -> int
   end

  val start_nt : initstate -> Gram.nonterminal

  val action_table : state -> action

  val goto_table : state -> Gram.nonterminal -> noninitstate option

  val past_symb_of_non_init_state : noninitstate -> Gram.symbol list

  val past_state_of_non_init_state : noninitstate -> (state -> bool) list

  val items_of_state : state -> item list

  val nullable_nterm : Gram.nonterminal -> bool

  val first_nterm : Gram.nonterminal -> Gram.terminal list
 end

module Coq0_Make =
 functor (A:Coq_T) ->
 struct
  (** val singleton_state_pred : A.state -> A.state -> bool **)

  let singleton_state_pred state0 state' =
    match compare1 A.coq_StateAlph.alphabetComparable state0 state' with
    | Eq -> true
    | _ -> false

  (** val past_state_of_state : A.state -> (A.state -> bool) list **)

  let past_state_of_state = function
  | A.Init _ -> []
  | A.Ninit nis -> A.past_state_of_non_init_state nis

  (** val head_symbs_of_state : A.state -> A.Gram.symbol list **)

  let head_symbs_of_state = function
  | A.Init _ -> []
  | A.Ninit s ->
    (A.last_symb_of_non_init_state s) :: (A.past_symb_of_non_init_state s)

  (** val head_states_of_state : A.state -> (A.state -> bool) list **)

  let head_states_of_state state0 =
    (singleton_state_pred state0) :: (past_state_of_state state0)

  (** val is_prefix : A.Gram.symbol list -> A.Gram.symbol list -> bool **)

  let rec is_prefix l1 l2 =
    match l1 with
    | [] -> true
    | t1 :: q1 ->
      (match l2 with
       | [] -> false
       | t2 :: q2 ->
         (&&) (compare_eqb A.Gram.coq_SymbolAlph.alphabetComparable t1 t2)
           (is_prefix q1 q2))

  (** val is_prefix_pred :
      (A.state -> bool) list -> (A.state -> bool) list -> bool **)

  let rec is_prefix_pred l1 l2 =
    match l1 with
    | [] -> true
    | f1 :: q1 ->
      (match l2 with
       | [] -> false
       | f2 :: q2 ->
         (&&)
           (forallb (fun x -> implb (f2 x) (f1 x))
             (all_list A.coq_StateAlph.alphabetFinite)) (is_prefix_pred q1 q2))

  (** val is_state_valid_after_pop :
      A.state -> A.Gram.symbol list -> (A.state -> bool) list -> bool **)

  let rec is_state_valid_after_pop state0 to_pop = function
  | [] -> true
  | p :: pl ->
    (match to_pop with
     | [] -> p state0
     | _ :: sl -> is_state_valid_after_pop state0 sl pl)

  (** val is_safe : unit -> bool **)

  let is_safe _ =
    if forallb (fun x ->
         match A.action_table x with
         | A.Default_reduce_act _ -> true
         | A.Lookahead_act l ->
           forallb (fun x0 ->
             match l x0 with
             | A.Shift_act s ->
               is_prefix (A.past_symb_of_non_init_state s)
                 (head_symbs_of_state x)
             | _ -> true) (all_list A.Gram.coq_TerminalAlph.alphabetFinite))
         (all_list A.coq_StateAlph.alphabetFinite)
    then if forallb (fun x ->
              forallb (fun x0 ->
                match A.goto_table x x0 with
                | Some a ->
                  is_prefix (A.past_symb_of_non_init_state a)
                    (head_symbs_of_state x)
                | None -> true)
                (all_list A.Gram.coq_NonTerminalAlph.alphabetFinite))
              (all_list A.coq_StateAlph.alphabetFinite)
         then if forallb (fun x ->
                   match A.action_table x with
                   | A.Default_reduce_act _ -> true
                   | A.Lookahead_act l ->
                     forallb (fun x0 ->
                       match l x0 with
                       | A.Shift_act s ->
                         is_prefix_pred (A.past_state_of_non_init_state s)
                           (head_states_of_state x)
                       | _ -> true)
                       (all_list A.Gram.coq_TerminalAlph.alphabetFinite))
                   (all_list A.coq_StateAlph.alphabetFinite)
              then if forallb (fun x ->
                        forallb (fun x0 ->
                          match A.goto_table x x0 with
                          | Some a ->
                            is_prefix_pred (A.past_state_of_non_init_state a)
                              (head_states_of_state x)
                          | None -> true)
                          (all_list A.Gram.coq_NonTerminalAlph.alphabetFinite))
                        (all_list A.coq_StateAlph.alphabetFinite)
                   then forallb (fun x ->
                          match A.action_table x with
                          | A.Default_reduce_act p ->
                            if is_prefix (A.Gram.prod_rhs_rev p)
                                 (head_symbs_of_state x)
                            then forallb (fun x0 ->
                                   if is_state_valid_after_pop x0
                                        (A.Gram.prod_rhs_rev p)
                                        (head_states_of_state x)
                                   then (match A.goto_table x0
                                                 (A.Gram.prod_lhs p) with
                                         | Some _ -> true
                                         | None ->
                                           (match x0 with
                                            | A.Init i ->
                                              compare_eqb
                                                A.Gram.coq_NonTerminalAlph.alphabetComparable
                                                (A.Gram.prod_lhs p)
                                                (A.start_nt i)
                                            | A.Ninit _ -> false))
                                   else true)
                                   (all_list A.coq_StateAlph.alphabetFinite)
                            else false
                          | A.Lookahead_act l ->
                            forallb (fun x0 ->
                              match l x0 with
                              | A.Reduce_act p ->
                                if is_prefix (A.Gram.prod_rhs_rev p)
                                     (head_symbs_of_state x)
                                then forallb (fun x1 ->
                                       if is_state_valid_after_pop x1
                                            (A.Gram.prod_rhs_rev p)
                                            (head_states_of_state x)
                                       then (match A.goto_table x1
                                                     (A.Gram.prod_lhs p) with
                                             | Some _ -> true
                                             | None ->
                                               (match x1 with
                                                | A.Init i ->
                                                  compare_eqb
                                                    A.Gram.coq_NonTerminalAlph.alphabetComparable
                                                    (A.Gram.prod_lhs p)
                                                    (A.start_nt i)
                                                | A.Ninit _ -> false))
                                       else true)
                                       (all_list
                                         A.coq_StateAlph.alphabetFinite)
                                else false
                              | _ -> true)
                              (all_list
                                A.Gram.coq_TerminalAlph.alphabetFinite))
                          (all_list A.coq_StateAlph.alphabetFinite)
                   else false
              else false
         else false
    else false
 end

module Coq1_Make =
 functor (A:Coq_T) ->
 struct
  module ValidSafe = Coq0_Make(A)

  type coq_Decidable = bool

  (** val decide : coq_Decidable -> bool **)

  let decide decidable =
    decidable

  (** val comparable_decidable_eq :
      'a1 comparable -> 'a1 -> 'a1 -> coq_Decidable **)

  let comparable_decidable_eq c x y =
    let c0 = compare1 c x y in (match c0 with
                                | Eq -> true
                                | _ -> false)

  (** val list_decidable_eq :
      ('a1 -> 'a1 -> coq_Decidable) -> 'a1 list -> 'a1 list -> coq_Decidable **)

  let rec list_decidable_eq x l1 l2 =
    match l1 with
    | [] -> (match l2 with
             | [] -> true
             | _ :: _ -> false)
    | y :: l ->
      (match l2 with
       | [] -> false
       | a :: l0 -> if x y a then list_decidable_eq x l l0 else false)

  (** val cast : 'a1 -> 'a1 -> (unit -> coq_Decidable) -> 'a2 -> 'a2 **)

  let cast _ _ _ a =
    a

  type buffer = __buffer Lazy.t
  and __buffer =
  | Buf_cons of A.Gram.token * buffer

  (** val buf_head : buffer -> A.Gram.token **)

  let buf_head b =
    let Buf_cons (buf_head0, _) = Lazy.force b in buf_head0

  (** val buf_tail : buffer -> buffer **)

  let buf_tail b =
    let Buf_cons (_, buf_tail0) = Lazy.force b in buf_tail0

  (** val app_buf : A.Gram.token list -> buffer -> buffer **)

  let rec app_buf l buf =
    match l with
    | [] -> buf
    | t0 :: q -> lazy (Buf_cons (t0, (app_buf q buf)))

  type noninitstate_type = A.Gram.symbol_semantic_type

  type stack = (A.noninitstate, noninitstate_type) sigT list

  (** val state_of_stack : A.initstate -> stack -> A.state **)

  let state_of_stack init = function
  | [] -> A.Init init
  | s0 :: _ -> let ExistT (s, _) = s0 in A.Ninit s

  (** val state_stack_of_stack :
      A.initstate -> stack -> (A.state -> bool) list **)

  let state_stack_of_stack init stack0 =
    app
      (map (fun cell ->
        ValidSafe.singleton_state_pred (A.Ninit (projT1 cell))) stack0)
      ((ValidSafe.singleton_state_pred (A.Init init)) :: [])

  (** val symb_stack_of_stack : stack -> A.Gram.symbol list **)

  let symb_stack_of_stack stack0 =
    map (fun cell -> A.last_symb_of_non_init_state (projT1 cell)) stack0

  (** val pop :
      A.Gram.symbol list -> stack -> 'a1 arrows_right -> stack * 'a1 **)

  let rec pop symbols_to_pop stk action0 =
    match symbols_to_pop with
    | [] -> (stk, (Obj.magic action0))
    | t0 :: q ->
      (match stk with
       | [] -> assert false (* absurd case *)
       | s :: stack_rec ->
         let ExistT (state_cur, sem) = s in
         let sem_conv =
           cast (A.last_symb_of_non_init_state state_cur) t0 (fun _ ->
             comparable_decidable_eq A.Gram.coq_SymbolAlph.alphabetComparable
               (A.last_symb_of_non_init_state state_cur) t0) sem
         in
         pop q stack_rec (Obj.magic action0 sem_conv))

  type step_result =
  | Fail_sr_full of A.state * A.Gram.token
  | Accept_sr of A.Gram.symbol_semantic_type * buffer
  | Progress_sr of stack * buffer

  (** val step_result_rect :
      A.initstate -> (A.state -> A.Gram.token -> 'a1) ->
      (A.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
      'a1) -> step_result -> 'a1 **)

  let step_result_rect _ f f0 f1 = function
  | Fail_sr_full (s0, t0) -> f s0 t0
  | Accept_sr (s0, b) -> f0 s0 b
  | Progress_sr (s0, b) -> f1 s0 b

  (** val step_result_rec :
      A.initstate -> (A.state -> A.Gram.token -> 'a1) ->
      (A.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
      'a1) -> step_result -> 'a1 **)

  let step_result_rec _ f f0 f1 = function
  | Fail_sr_full (s0, t0) -> f s0 t0
  | Accept_sr (s0, b) -> f0 s0 b
  | Progress_sr (s0, b) -> f1 s0 b

  (** val reduce_step :
      A.initstate -> stack -> A.Gram.production -> buffer -> step_result **)

  let reduce_step init stk prod0 buffer0 =
    let (stk', sem) =
      pop (A.Gram.prod_rhs_rev prod0) stk (A.Gram.prod_action prod0)
    in
    (match A.goto_table (state_of_stack init stk') (A.Gram.prod_lhs prod0) with
     | Some s -> Progress_sr (((ExistT (s, sem)) :: stk'), buffer0)
     | None ->
       let sem0 =
         cast (A.Gram.NT (A.Gram.prod_lhs prod0)) (A.Gram.NT
           (A.start_nt init)) (fun _ ->
           comparable_decidable_eq A.Gram.coq_SymbolAlph.alphabetComparable
             (A.Gram.NT (A.Gram.prod_lhs prod0)) (A.Gram.NT (A.start_nt init)))
           sem
       in
       Accept_sr (sem0, buffer0))

  (** val step : A.initstate -> stack -> buffer -> step_result **)

  let step init stk buffer0 =
    match A.action_table (state_of_stack init stk) with
    | A.Default_reduce_act prod0 -> reduce_step init stk prod0 buffer0
    | A.Lookahead_act awt ->
      (match awt (A.Gram.token_term (buf_head buffer0)) with
       | A.Shift_act state_new ->
         let sem_conv = A.Gram.token_sem (buf_head buffer0) in
         Progress_sr (((ExistT (state_new, sem_conv)) :: stk),
         (buf_tail buffer0))
       | A.Reduce_act prod0 -> reduce_step init stk prod0 buffer0
       | A.Fail_act ->
         Fail_sr_full ((state_of_stack init stk), (buf_head buffer0)))

  (** val parse_fix : A.initstate -> stack -> buffer -> int -> step_result **)

  let rec parse_fix init stk buffer0 log_n_steps =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> step init stk buffer0)
      (fun log_n_steps0 ->
      match parse_fix init stk buffer0 log_n_steps0 with
      | Progress_sr (stk0, buffer1) ->
        parse_fix init stk0 buffer1 log_n_steps0
      | x -> x)
      log_n_steps

  type 'a parse_result =
  | Fail_pr_full of A.state * A.Gram.token
  | Timeout_pr
  | Parsed_pr of 'a * buffer

  (** val parse_result_rect :
      (A.state -> A.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2) ->
      'a1 parse_result -> 'a2 **)

  let parse_result_rect f f0 f1 = function
  | Fail_pr_full (s, t0) -> f s t0
  | Timeout_pr -> f0
  | Parsed_pr (a, b) -> f1 a b

  (** val parse_result_rec :
      (A.state -> A.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2) ->
      'a1 parse_result -> 'a2 **)

  let parse_result_rec f f0 f1 = function
  | Fail_pr_full (s, t0) -> f s t0
  | Timeout_pr -> f0
  | Parsed_pr (a, b) -> f1 a b

  (** val parse :
      A.initstate -> buffer -> int -> A.Gram.symbol_semantic_type parse_result **)

  let parse init buffer0 log_n_steps =
    match parse_fix init [] buffer0 log_n_steps with
    | Fail_sr_full (st, tok) -> Fail_pr_full (st, tok)
    | Accept_sr (sem, buffer') -> Parsed_pr (sem, buffer')
    | Progress_sr (_, _) -> Timeout_pr
 end

module Coq2_Make =
 functor (A:Coq_T) ->
 functor (Inter:sig
  module ValidSafe :
   sig
    val singleton_state_pred : A.state -> A.state -> bool

    val past_state_of_state : A.state -> (A.state -> bool) list

    val head_symbs_of_state : A.state -> A.Gram.symbol list

    val head_states_of_state : A.state -> (A.state -> bool) list

    val is_prefix : A.Gram.symbol list -> A.Gram.symbol list -> bool

    val is_prefix_pred :
      (A.state -> bool) list -> (A.state -> bool) list -> bool

    val is_state_valid_after_pop :
      A.state -> A.Gram.symbol list -> (A.state -> bool) list -> bool

    val is_safe : unit -> bool
   end

  type coq_Decidable = bool

  val decide : coq_Decidable -> bool

  val comparable_decidable_eq : 'a1 comparable -> 'a1 -> 'a1 -> coq_Decidable

  val list_decidable_eq :
    ('a1 -> 'a1 -> coq_Decidable) -> 'a1 list -> 'a1 list -> coq_Decidable

  val cast : 'a1 -> 'a1 -> (unit -> coq_Decidable) -> 'a2 -> 'a2

  type buffer = __buffer Lazy.t
  and __buffer =
  | Buf_cons of A.Gram.token * buffer

  val buf_head : buffer -> A.Gram.token

  val buf_tail : buffer -> buffer

  val app_buf : A.Gram.token list -> buffer -> buffer

  type noninitstate_type = A.Gram.symbol_semantic_type

  type stack = (A.noninitstate, noninitstate_type) sigT list

  val state_of_stack : A.initstate -> stack -> A.state

  val state_stack_of_stack : A.initstate -> stack -> (A.state -> bool) list

  val symb_stack_of_stack : stack -> A.Gram.symbol list

  val pop : A.Gram.symbol list -> stack -> 'a1 arrows_right -> stack * 'a1

  type step_result =
  | Fail_sr_full of A.state * A.Gram.token
  | Accept_sr of A.Gram.symbol_semantic_type * buffer
  | Progress_sr of stack * buffer

  val step_result_rect :
    A.initstate -> (A.state -> A.Gram.token -> 'a1) ->
    (A.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
    'a1) -> step_result -> 'a1

  val step_result_rec :
    A.initstate -> (A.state -> A.Gram.token -> 'a1) ->
    (A.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
    'a1) -> step_result -> 'a1

  val reduce_step :
    A.initstate -> stack -> A.Gram.production -> buffer -> step_result

  val step : A.initstate -> stack -> buffer -> step_result

  val parse_fix : A.initstate -> stack -> buffer -> int -> step_result

  type 'a parse_result =
  | Fail_pr_full of A.state * A.Gram.token
  | Timeout_pr
  | Parsed_pr of 'a * buffer

  val parse_result_rect :
    (A.state -> A.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2) -> 'a1
    parse_result -> 'a2

  val parse_result_rec :
    (A.state -> A.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2) -> 'a1
    parse_result -> 'a2

  val parse :
    A.initstate -> buffer -> int -> A.Gram.symbol_semantic_type parse_result
 end) ->
 struct
 end

module Coq3_Make =
 functor (A:Coq_T) ->
 struct
  module TerminalComparableM =
   struct
    type t = A.Gram.terminal

    (** val tComparable : t comparable **)

    let tComparable =
      A.Gram.coq_TerminalAlph.alphabetComparable
   end

  module TerminalOrderedType =
   OrderedType_from_ComparableM(TerminalComparableM)

  module StateProdPosComparableM =
   struct
    type t = (A.state * A.Gram.production) * int

    (** val tComparable : t comparable **)

    let tComparable =
      pairComparable
        (pairComparable A.coq_StateAlph.alphabetComparable
          A.Gram.coq_ProductionAlph.alphabetComparable) natComparable
   end

  module StateProdPosOrderedType =
   OrderedType_from_ComparableM(StateProdPosComparableM)

  module TerminalSet = Make(TerminalOrderedType)

  module StateProdPosMap = Coq_Make(StateProdPosOrderedType)

  (** val nullable_symb : A.Gram.symbol -> bool **)

  let nullable_symb = function
  | A.Gram.T _ -> false
  | A.Gram.NT nt -> A.nullable_nterm nt

  (** val nullable_word : A.Gram.symbol list -> bool **)

  let nullable_word word =
    forallb nullable_symb word

  (** val first_nterm_set : A.Gram.nonterminal -> TerminalSet.t **)

  let first_nterm_set nterm =
    fold_left (fun acc t0 -> TerminalSet.add t0 acc) (A.first_nterm nterm)
      TerminalSet.empty

  (** val first_symb_set : A.Gram.symbol -> TerminalSet.t **)

  let first_symb_set = function
  | A.Gram.T t0 -> TerminalSet.singleton t0
  | A.Gram.NT nt -> first_nterm_set nt

  (** val first_word_set : A.Gram.symbol list -> TerminalSet.t **)

  let rec first_word_set = function
  | [] -> TerminalSet.empty
  | t0 :: q ->
    if nullable_symb t0
    then TerminalSet.union (first_symb_set t0) (first_word_set q)
    else first_symb_set t0

  (** val future_of_prod : A.Gram.production -> int -> A.Gram.symbol list **)

  let future_of_prod prod0 dot_pos =
    let rec loop n0 lst =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> lst)
        (fun x -> match loop x lst with
                  | [] -> []
                  | _ :: q -> q)
        n0
    in loop dot_pos (rev' (A.Gram.prod_rhs_rev prod0))

  (** val items_map : unit -> TerminalSet.t StateProdPosMap.t **)

  let items_map _ =
    fold_left (fun acc state0 ->
      fold_left (fun acc0 item0 ->
        let key0 = ((state0, (A.prod_item item0)), (A.dot_pos_item item0)) in
        let data =
          fold_left (fun acc1 t0 -> TerminalSet.add t0 acc1)
            (A.lookaheads_item item0) TerminalSet.empty
        in
        let old =
          match StateProdPosMap.find key0 acc0 with
          | Some x -> x
          | None -> TerminalSet.empty
        in
        StateProdPosMap.add key0 (TerminalSet.union data old) acc0)
        (A.items_of_state state0) acc)
      (all_list A.coq_StateAlph.alphabetFinite) StateProdPosMap.empty

  (** val find_items_map :
      TerminalSet.t StateProdPosMap.t -> A.state -> A.Gram.production -> int
      -> TerminalSet.t **)

  let find_items_map items_map0 state0 prod0 dot_pos =
    match StateProdPosMap.find ((state0, prod0), dot_pos) items_map0 with
    | Some x -> x
    | None -> TerminalSet.empty

  (** val forallb_items :
      TerminalSet.t StateProdPosMap.t -> (A.state -> A.Gram.production -> int
      -> TerminalSet.t -> bool) -> bool **)

  let forallb_items items_map0 p =
    StateProdPosMap.fold (fun key0 set acc ->
      let (p0, pos) = key0 in let (st, p1) = p0 in (&&) acc (p st p1 pos set))
      items_map0 true

  (** val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool **)

  let is_end_reduce items_map0 =
    forallb_items items_map0 (fun s prod0 pos lset ->
      match future_of_prod prod0 pos with
      | [] ->
        (match A.action_table s with
         | A.Default_reduce_act p ->
           compare_eqb A.Gram.coq_ProductionAlph.alphabetComparable p prod0
         | A.Lookahead_act awt ->
           TerminalSet.fold (fun lookahead acc ->
             match awt lookahead with
             | A.Reduce_act p ->
               (&&) acc
                 (compare_eqb A.Gram.coq_ProductionAlph.alphabetComparable p
                   prod0)
             | _ -> false) lset true)
      | _ :: _ -> true)

  (** val is_complete_0 : TerminalSet.t StateProdPosMap.t -> bool **)

  let is_complete_0 im =
    if forallb (fun x ->
         if nullable_word (A.Gram.prod_rhs_rev x)
         then A.nullable_nterm (A.Gram.prod_lhs x)
         else true) (all_list A.Gram.coq_ProductionAlph.alphabetFinite)
    then if forallb (fun x ->
              TerminalSet.subset
                (first_word_set (rev' (A.Gram.prod_rhs_rev x)))
                (first_nterm_set (A.Gram.prod_lhs x)))
              (all_list A.Gram.coq_ProductionAlph.alphabetFinite)
         then if forallb (fun x ->
                   forallb (fun x0 ->
                     if compare_eqb
                          A.Gram.coq_NonTerminalAlph.alphabetComparable
                          (A.Gram.prod_lhs x0) (A.start_nt x)
                     then forallb (fun t0 ->
                            TerminalSet.mem t0
                              (find_items_map im (A.Init x) x0 0))
                            (all_list A.Gram.coq_TerminalAlph.alphabetFinite)
                     else true)
                     (all_list A.Gram.coq_ProductionAlph.alphabetFinite))
                   (all_list A.coq_InitStateAlph.alphabetFinite)
              then if forallb_items im (fun st prod0 pos lset ->
                        match future_of_prod prod0 pos with
                        | [] -> true
                        | s :: _ ->
                          (match s with
                           | A.Gram.T t0 ->
                             (match A.action_table st with
                              | A.Default_reduce_act _ -> false
                              | A.Lookahead_act l ->
                                (match l t0 with
                                 | A.Shift_act s0 ->
                                   TerminalSet.subset lset
                                     (find_items_map im (A.Ninit s0) prod0
                                       (Stdlib.Int.succ pos))
                                 | _ -> false))
                           | A.Gram.NT _ -> true))
                   then if forallb_items im (fun st prod0 pos lset ->
                             match future_of_prod prod0 pos with
                             | [] ->
                               (match A.action_table st with
                                | A.Default_reduce_act p ->
                                  compare_eqb
                                    A.Gram.coq_ProductionAlph.alphabetComparable
                                    p prod0
                                | A.Lookahead_act l ->
                                  TerminalSet.fold (fun lookahead acc ->
                                    if acc
                                    then (match l lookahead with
                                          | A.Reduce_act p ->
                                            compare_eqb
                                              A.Gram.coq_ProductionAlph.alphabetComparable
                                              p prod0
                                          | _ -> false)
                                    else false) lset true)
                             | _ :: _ -> true)
                        then if forallb_items im (fun st prod0 pos lset ->
                                  match future_of_prod prod0 pos with
                                  | [] -> true
                                  | s :: _ ->
                                    (match s with
                                     | A.Gram.T _ -> true
                                     | A.Gram.NT n0 ->
                                       (match A.goto_table st n0 with
                                        | Some a ->
                                          TerminalSet.subset lset
                                            (find_items_map im (A.Ninit a)
                                              prod0 (Stdlib.Int.succ pos))
                                        | None -> false)))
                             then if forallb (fun x ->
                                       match A.goto_table (A.Init x)
                                               (A.start_nt x) with
                                       | Some _ -> false
                                       | None -> true)
                                       (all_list
                                         A.coq_InitStateAlph.alphabetFinite)
                                  then forallb_items im
                                         (fun st prod0 pos lset ->
                                         match future_of_prod prod0 pos with
                                         | [] -> true
                                         | s :: fut' ->
                                           (match s with
                                            | A.Gram.T _ -> true
                                            | A.Gram.NT n0 ->
                                              forallb (fun x ->
                                                if compare_eqb
                                                     A.Gram.coq_NonTerminalAlph.alphabetComparable
                                                     (A.Gram.prod_lhs x) n0
                                                then if if nullable_word fut'
                                                        then TerminalSet.subset
                                                               lset
                                                               (find_items_map
                                                                 im st x 0)
                                                        else true
                                                     then TerminalSet.subset
                                                            (first_word_set
                                                              fut')
                                                            (find_items_map
                                                              im st x 0)
                                                     else false
                                                else true)
                                                (all_list
                                                  A.Gram.coq_ProductionAlph.alphabetFinite)))
                                  else false
                             else false
                        else false
                   else false
              else false
         else false
    else false

  (** val is_complete : unit -> bool **)

  let is_complete _ =
    is_complete_0 (items_map ())
 end

module Coq4_Make =
 functor (A:Coq_T) ->
 functor (Inter:sig
  module ValidSafe :
   sig
    val singleton_state_pred : A.state -> A.state -> bool

    val past_state_of_state : A.state -> (A.state -> bool) list

    val head_symbs_of_state : A.state -> A.Gram.symbol list

    val head_states_of_state : A.state -> (A.state -> bool) list

    val is_prefix : A.Gram.symbol list -> A.Gram.symbol list -> bool

    val is_prefix_pred :
      (A.state -> bool) list -> (A.state -> bool) list -> bool

    val is_state_valid_after_pop :
      A.state -> A.Gram.symbol list -> (A.state -> bool) list -> bool

    val is_safe : unit -> bool
   end

  type coq_Decidable = bool

  val decide : coq_Decidable -> bool

  val comparable_decidable_eq : 'a1 comparable -> 'a1 -> 'a1 -> coq_Decidable

  val list_decidable_eq :
    ('a1 -> 'a1 -> coq_Decidable) -> 'a1 list -> 'a1 list -> coq_Decidable

  val cast : 'a1 -> 'a1 -> (unit -> coq_Decidable) -> 'a2 -> 'a2

  type buffer = __buffer Lazy.t
  and __buffer =
  | Buf_cons of A.Gram.token * buffer

  val buf_head : buffer -> A.Gram.token

  val buf_tail : buffer -> buffer

  val app_buf : A.Gram.token list -> buffer -> buffer

  type noninitstate_type = A.Gram.symbol_semantic_type

  type stack = (A.noninitstate, noninitstate_type) sigT list

  val state_of_stack : A.initstate -> stack -> A.state

  val state_stack_of_stack : A.initstate -> stack -> (A.state -> bool) list

  val symb_stack_of_stack : stack -> A.Gram.symbol list

  val pop : A.Gram.symbol list -> stack -> 'a1 arrows_right -> stack * 'a1

  type step_result =
  | Fail_sr_full of A.state * A.Gram.token
  | Accept_sr of A.Gram.symbol_semantic_type * buffer
  | Progress_sr of stack * buffer

  val step_result_rect :
    A.initstate -> (A.state -> A.Gram.token -> 'a1) ->
    (A.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
    'a1) -> step_result -> 'a1

  val step_result_rec :
    A.initstate -> (A.state -> A.Gram.token -> 'a1) ->
    (A.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
    'a1) -> step_result -> 'a1

  val reduce_step :
    A.initstate -> stack -> A.Gram.production -> buffer -> step_result

  val step : A.initstate -> stack -> buffer -> step_result

  val parse_fix : A.initstate -> stack -> buffer -> int -> step_result

  type 'a parse_result =
  | Fail_pr_full of A.state * A.Gram.token
  | Timeout_pr
  | Parsed_pr of 'a * buffer

  val parse_result_rect :
    (A.state -> A.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2) -> 'a1
    parse_result -> 'a2

  val parse_result_rec :
    (A.state -> A.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2) -> 'a1
    parse_result -> 'a2

  val parse :
    A.initstate -> buffer -> int -> A.Gram.symbol_semantic_type parse_result
 end) ->
 struct
  module Valid = Coq3_Make(A)

  type pt_zipper =
  | Top_ptz
  | Cons_ptl_ptz of A.Gram.symbol list * A.Gram.token list
     * A.GramDefs.parse_tree_list * A.Gram.symbol * A.Gram.token list
     * ptl_zipper
  and ptl_zipper =
  | Non_terminal_pt_ptlz of A.Gram.production * A.Gram.token list * pt_zipper
  | Cons_ptl_ptlz of A.Gram.symbol list * A.Gram.token list * A.Gram.symbol
     * A.Gram.token list * A.GramDefs.parse_tree * ptl_zipper

  (** val pt_zipper_rect :
      A.initstate -> A.Gram.token list -> 'a1 -> (A.Gram.symbol list ->
      A.Gram.token list -> A.GramDefs.parse_tree_list -> A.Gram.symbol ->
      A.Gram.token list -> ptl_zipper -> 'a1) -> A.Gram.symbol ->
      A.Gram.token list -> pt_zipper -> 'a1 **)

  let pt_zipper_rect _ _ f f0 _ _ = function
  | Top_ptz -> f
  | Cons_ptl_ptz (head_symbolsq, wordq, p0, head_symbolt, wordt, p1) ->
    f0 head_symbolsq wordq p0 head_symbolt wordt p1

  (** val pt_zipper_rec :
      A.initstate -> A.Gram.token list -> 'a1 -> (A.Gram.symbol list ->
      A.Gram.token list -> A.GramDefs.parse_tree_list -> A.Gram.symbol ->
      A.Gram.token list -> ptl_zipper -> 'a1) -> A.Gram.symbol ->
      A.Gram.token list -> pt_zipper -> 'a1 **)

  let pt_zipper_rec _ _ f f0 _ _ = function
  | Top_ptz -> f
  | Cons_ptl_ptz (head_symbolsq, wordq, p0, head_symbolt, wordt, p1) ->
    f0 head_symbolsq wordq p0 head_symbolt wordt p1

  (** val ptl_zipper_rect :
      A.initstate -> A.Gram.token list -> (A.Gram.production -> A.Gram.token
      list -> pt_zipper -> 'a1) -> (A.Gram.symbol list -> A.Gram.token list
      -> A.Gram.symbol -> A.Gram.token list -> A.GramDefs.parse_tree ->
      ptl_zipper -> 'a1 -> 'a1) -> A.Gram.symbol list -> A.Gram.token list ->
      ptl_zipper -> 'a1 **)

  let rec ptl_zipper_rect init full_word f f0 _ _ = function
  | Non_terminal_pt_ptlz (p0, word, p1) -> f p0 word p1
  | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, p0, p1) ->
    f0 head_symbolsq wordq head_symbolt wordt p0 p1
      (ptl_zipper_rect init full_word f f0 (head_symbolt :: head_symbolsq)
        (app wordq wordt) p1)

  (** val ptl_zipper_rec :
      A.initstate -> A.Gram.token list -> (A.Gram.production -> A.Gram.token
      list -> pt_zipper -> 'a1) -> (A.Gram.symbol list -> A.Gram.token list
      -> A.Gram.symbol -> A.Gram.token list -> A.GramDefs.parse_tree ->
      ptl_zipper -> 'a1 -> 'a1) -> A.Gram.symbol list -> A.Gram.token list ->
      ptl_zipper -> 'a1 **)

  let rec ptl_zipper_rec init full_word f f0 _ _ = function
  | Non_terminal_pt_ptlz (p0, word, p1) -> f p0 word p1
  | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, p0, p1) ->
    f0 head_symbolsq wordq head_symbolt wordt p0 p1
      (ptl_zipper_rec init full_word f f0 (head_symbolt :: head_symbolsq)
        (app wordq wordt) p1)

  type pt_dot =
  | Reduce_ptd of A.Gram.production * A.Gram.token list
     * A.GramDefs.parse_tree_list * pt_zipper
  | Shift_ptd of A.Gram.token * A.Gram.symbol list * A.Gram.token list
     * A.GramDefs.parse_tree_list * ptl_zipper

  (** val pt_dot_rect :
      A.initstate -> A.Gram.token list -> (A.Gram.production -> A.Gram.token
      list -> A.GramDefs.parse_tree_list -> pt_zipper -> 'a1) ->
      (A.Gram.token -> A.Gram.symbol list -> A.Gram.token list ->
      A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1 **)

  let pt_dot_rect _ _ f f0 = function
  | Reduce_ptd (prod0, word, p0, p1) -> f prod0 word p0 p1
  | Shift_ptd (tok, symbolsq, wordq, p0, p1) -> f0 tok symbolsq wordq p0 p1

  (** val pt_dot_rec :
      A.initstate -> A.Gram.token list -> (A.Gram.production -> A.Gram.token
      list -> A.GramDefs.parse_tree_list -> pt_zipper -> 'a1) ->
      (A.Gram.token -> A.Gram.symbol list -> A.Gram.token list ->
      A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1 **)

  let pt_dot_rec _ _ f f0 = function
  | Reduce_ptd (prod0, word, p0, p1) -> f prod0 word p0 p1
  | Shift_ptd (tok, symbolsq, wordq, p0, p1) -> f0 tok symbolsq wordq p0 p1

  (** val ptlz_sem :
      A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
      list -> ptl_zipper -> (__ -> __ arrows_right -> __) ->
      A.Gram.symbol_semantic_type **)

  let ptlz_sem _ _ =
    let rec ptlz_sem0 _ _ ptlz k =
      match ptlz with
      | Non_terminal_pt_ptlz (prod0, word, ptz) ->
        ptz_sem0 (A.Gram.NT (A.Gram.prod_lhs prod0)) word ptz
          (k __ (A.Gram.prod_action prod0))
      | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, pt, ptlz0) ->
        Obj.magic ptlz_sem0 (head_symbolt :: head_symbolsq) (app wordq wordt)
          ptlz0 (fun _ f ->
          k __ (f (A.GramDefs.pt_sem head_symbolt wordt pt)))
    and ptz_sem0 _ _ ptz sem =
      match ptz with
      | Top_ptz -> Obj.magic sem
      | Cons_ptl_ptz (head_symbolsq, wordq, ptl, head_symbolt, wordt, ptlz) ->
        Obj.magic ptlz_sem0 (head_symbolt :: head_symbolsq) (app wordq wordt)
          ptlz (fun _ f -> A.GramDefs.ptl_sem head_symbolsq wordq ptl (f sem))
    in ptlz_sem0

  (** val ptz_sem :
      A.initstate -> A.Gram.token list -> A.Gram.symbol -> A.Gram.token list
      -> pt_zipper -> A.Gram.symbol_semantic_type ->
      A.Gram.symbol_semantic_type **)

  let ptz_sem _ _ =
    let rec ptlz_sem0 _ _ ptlz k =
      match ptlz with
      | Non_terminal_pt_ptlz (prod0, word, ptz) ->
        ptz_sem0 (A.Gram.NT (A.Gram.prod_lhs prod0)) word ptz
          (k __ (A.Gram.prod_action prod0))
      | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, pt, ptlz0) ->
        Obj.magic ptlz_sem0 (head_symbolt :: head_symbolsq) (app wordq wordt)
          ptlz0 (fun _ f ->
          k __ (f (A.GramDefs.pt_sem head_symbolt wordt pt)))
    and ptz_sem0 _ _ ptz sem =
      match ptz with
      | Top_ptz -> sem
      | Cons_ptl_ptz (head_symbolsq, wordq, ptl, head_symbolt, wordt, ptlz) ->
        Obj.magic ptlz_sem0 (head_symbolt :: head_symbolsq) (app wordq wordt)
          ptlz (fun _ f -> A.GramDefs.ptl_sem head_symbolsq wordq ptl (f sem))
    in ptz_sem0

  (** val ptd_sem :
      A.initstate -> A.Gram.token list -> pt_dot ->
      A.Gram.symbol_semantic_type **)

  let ptd_sem init full_word = function
  | Reduce_ptd (prod0, word, ptl, ptz) ->
    ptz_sem init full_word (A.Gram.NT (A.Gram.prod_lhs prod0)) word ptz
      (A.GramDefs.ptl_sem (A.Gram.prod_rhs_rev prod0) word ptl
        (A.Gram.prod_action prod0))
  | Shift_ptd (tok, symbolsq, wordq, ptl, ptlz) ->
    ptlz_sem init full_word ((A.Gram.T (A.Gram.token_term tok)) :: symbolsq)
      (app wordq (tok :: [])) ptlz (fun _ f ->
      A.GramDefs.ptl_sem symbolsq wordq ptl
        (Obj.magic f (A.Gram.token_sem tok)))

  (** val ptlz_buffer :
      A.initstate -> A.Gram.token list -> Inter.buffer -> A.Gram.symbol list
      -> A.Gram.token list -> ptl_zipper -> Inter.buffer **)

  let ptlz_buffer _ _ buffer_end =
    let rec ptlz_buffer0 _ _ = function
    | Non_terminal_pt_ptlz (p, word, ptz) ->
      ptz_buffer0 (A.Gram.NT (A.Gram.prod_lhs p)) word ptz
    | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, _, ptlz') ->
      Inter.app_buf wordt
        (ptlz_buffer0 (head_symbolt :: head_symbolsq) (app wordq wordt) ptlz')
    and ptz_buffer0 _ _ = function
    | Top_ptz -> buffer_end
    | Cons_ptl_ptz (head_symbolsq, wordq, _, head_symbolt, wordt, ptlz) ->
      ptlz_buffer0 (head_symbolt :: head_symbolsq) (app wordq wordt) ptlz
    in ptlz_buffer0

  (** val ptz_buffer :
      A.initstate -> A.Gram.token list -> Inter.buffer -> A.Gram.symbol ->
      A.Gram.token list -> pt_zipper -> Inter.buffer **)

  let ptz_buffer _ _ buffer_end =
    let rec ptlz_buffer0 _ _ = function
    | Non_terminal_pt_ptlz (p, word, ptz) ->
      ptz_buffer0 (A.Gram.NT (A.Gram.prod_lhs p)) word ptz
    | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, _, ptlz') ->
      Inter.app_buf wordt
        (ptlz_buffer0 (head_symbolt :: head_symbolsq) (app wordq wordt) ptlz')
    and ptz_buffer0 _ _ = function
    | Top_ptz -> buffer_end
    | Cons_ptl_ptz (head_symbolsq, wordq, _, head_symbolt, wordt, ptlz) ->
      ptlz_buffer0 (head_symbolt :: head_symbolsq) (app wordq wordt) ptlz
    in ptz_buffer0

  (** val ptd_buffer :
      A.initstate -> A.Gram.token list -> Inter.buffer -> pt_dot ->
      Inter.buffer **)

  let ptd_buffer init full_word buffer_end = function
  | Reduce_ptd (prod0, word, _, ptz) ->
    ptz_buffer init full_word buffer_end (A.Gram.NT (A.Gram.prod_lhs prod0))
      word ptz
  | Shift_ptd (tok, symbolsq, wordq, _, ptlz) ->
    lazy (Inter.Buf_cons (tok,
      (ptlz_buffer init full_word buffer_end ((A.Gram.T
        (A.Gram.token_term tok)) :: symbolsq) (app wordq (tok :: [])) ptlz)))

  (** val ptlz_prod :
      A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
      list -> ptl_zipper -> A.Gram.production **)

  let rec ptlz_prod init full_word _ _ = function
  | Non_terminal_pt_ptlz (prod0, _, _) -> prod0
  | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, _, ptlz') ->
    ptlz_prod init full_word (head_symbolt :: head_symbolsq)
      (app wordq wordt) ptlz'

  (** val ptlz_future :
      A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
      list -> ptl_zipper -> A.Gram.symbol list **)

  let rec ptlz_future init full_word _ _ = function
  | Non_terminal_pt_ptlz (_, _, _) -> []
  | Cons_ptl_ptlz (head_symbolsq, wordq, s, wordt, _, ptlz') ->
    s :: (ptlz_future init full_word (s :: head_symbolsq) (app wordq wordt)
           ptlz')

  (** val ptlz_lookahead :
      A.initstate -> A.Gram.token list -> Inter.buffer -> A.Gram.symbol list
      -> A.Gram.token list -> ptl_zipper -> A.Gram.terminal **)

  let rec ptlz_lookahead init full_word buffer_end _ _ = function
  | Non_terminal_pt_ptlz (p, word, ptz) ->
    A.Gram.token_term
      (Inter.buf_head
        (ptz_buffer init full_word buffer_end (A.Gram.NT (A.Gram.prod_lhs p))
          word ptz))
  | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, _, ptlz') ->
    ptlz_lookahead init full_word buffer_end (head_symbolt :: head_symbolsq)
      (app wordq wordt) ptlz'

  (** val build_pt_dot_from_pt :
      A.initstate -> A.Gram.token list -> A.Gram.symbol -> A.Gram.token list
      -> A.GramDefs.parse_tree -> pt_zipper -> pt_dot **)

  let build_pt_dot_from_pt _ _ =
    let rec build_pt_dot_from_pt0 _ _ pt ptz =
      match pt with
      | A.GramDefs.Terminal_pt tok ->
        let x =
          match ptz with
          | Top_ptz -> assert false (* absurd case *)
          | Cons_ptl_ptz (head_symbolsq, wordq, ptl, _, _, ptlz) ->
            ExistT (head_symbolsq, (ExistT (wordq, (ptl, ptlz))))
        in
        Shift_ptd (tok, (projT1 x), (projT1 (projT2 x)),
        (fst (projT2 (projT2 x))), (snd (projT2 (projT2 x))))
      | A.GramDefs.Non_terminal_pt (prod0, word0, ptl) ->
        let is_notnil =
          match ptl with
          | A.GramDefs.Nil_ptl -> None
          | A.GramDefs.Cons_ptl (_, _, _, _, _, _) -> Some __
        in
        (match is_notnil with
         | Some _ ->
           build_pt_dot_from_pt_rec0 (A.Gram.prod_rhs_rev prod0) word0 ptl __
             (Non_terminal_pt_ptlz (prod0, word0, ptz))
         | None -> Reduce_ptd (prod0, word0, ptl, ptz))
    and build_pt_dot_from_pt_rec0 _ _ ptl _ ptlz =
      match ptl with
      | A.GramDefs.Nil_ptl -> assert false (* absurd case *)
      | A.GramDefs.Cons_ptl (_, _, ptl', head_symbolt, wordt, pt) ->
        (match ptl' with
         | A.GramDefs.Nil_ptl ->
           build_pt_dot_from_pt0 head_symbolt wordt pt (Cons_ptl_ptz ([], [],
             A.GramDefs.Nil_ptl, head_symbolt, wordt, ptlz))
         | A.GramDefs.Cons_ptl (head_symbolsq, wordq, _, head_symbolt0,
                                wordt0, _) ->
           build_pt_dot_from_pt_rec0 (head_symbolt0 :: head_symbolsq)
             (app wordq wordt0) ptl' __ (Cons_ptl_ptlz
             ((head_symbolt0 :: head_symbolsq), (app wordq wordt0),
             head_symbolt, wordt, pt, ptlz)))
    in build_pt_dot_from_pt0

  (** val build_pt_dot_from_pt_rec :
      A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
      list -> A.GramDefs.parse_tree_list -> ptl_zipper -> pt_dot **)

  let build_pt_dot_from_pt_rec _ _ symbs word ptl ptlz =
    let rec build_pt_dot_from_pt0 _ _ pt ptz =
      match pt with
      | A.GramDefs.Terminal_pt tok ->
        let x =
          match ptz with
          | Top_ptz -> assert false (* absurd case *)
          | Cons_ptl_ptz (head_symbolsq, wordq, ptl0, _, _, ptlz0) ->
            ExistT (head_symbolsq, (ExistT (wordq, (ptl0, ptlz0))))
        in
        Shift_ptd (tok, (projT1 x), (projT1 (projT2 x)),
        (fst (projT2 (projT2 x))), (snd (projT2 (projT2 x))))
      | A.GramDefs.Non_terminal_pt (prod0, word0, ptl0) ->
        let is_notnil =
          match ptl0 with
          | A.GramDefs.Nil_ptl -> None
          | A.GramDefs.Cons_ptl (_, _, _, _, _, _) -> Some __
        in
        (match is_notnil with
         | Some _ ->
           build_pt_dot_from_pt_rec0 (A.Gram.prod_rhs_rev prod0) word0 ptl0
             (Non_terminal_pt_ptlz (prod0, word0, ptz))
         | None -> Reduce_ptd (prod0, word0, ptl0, ptz))
    and build_pt_dot_from_pt_rec0 _ _ ptl0 ptlz0 =
      match ptl0 with
      | A.GramDefs.Nil_ptl -> assert false (* absurd case *)
      | A.GramDefs.Cons_ptl (_, _, ptl', head_symbolt, wordt, pt) ->
        (match ptl' with
         | A.GramDefs.Nil_ptl ->
           build_pt_dot_from_pt0 head_symbolt wordt pt (Cons_ptl_ptz ([], [],
             A.GramDefs.Nil_ptl, head_symbolt, wordt, ptlz0))
         | A.GramDefs.Cons_ptl (head_symbolsq, wordq, _, head_symbolt0,
                                wordt0, _) ->
           build_pt_dot_from_pt_rec0 (head_symbolt0 :: head_symbolsq)
             (app wordq wordt0) ptl' (Cons_ptl_ptlz
             ((head_symbolt0 :: head_symbolsq), (app wordq wordt0),
             head_symbolt, wordt, pt, ptlz0)))
    in build_pt_dot_from_pt_rec0 symbs word ptl ptlz

  (** val build_pt_dot_from_ptl :
      A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
      list -> A.GramDefs.parse_tree_list -> ptl_zipper -> pt_dot **)

  let build_pt_dot_from_ptl init full_word _ _ ptl = function
  | Non_terminal_pt_ptlz (p, word0, ptz) -> Reduce_ptd (p, word0, ptl, ptz)
  | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, pt, ptlz0) ->
    build_pt_dot_from_pt init full_word head_symbolt wordt pt (Cons_ptl_ptz
      (head_symbolsq, wordq, ptl, head_symbolt, wordt, ptlz0))

  (** val next_ptd :
      A.initstate -> A.Gram.token list -> pt_dot -> pt_dot option **)

  let next_ptd init full_word = function
  | Reduce_ptd (prod0, word, ptl, ptz) ->
    let x = A.GramDefs.Non_terminal_pt (prod0, word, ptl) in
    (match ptz with
     | Top_ptz -> None
     | Cons_ptl_ptz (head_symbolsq, wordq, ptl', head_symbolt, wordt, ptlz) ->
       Some
         (build_pt_dot_from_ptl init full_word
           (head_symbolt :: head_symbolsq) (app wordq wordt)
           (A.GramDefs.Cons_ptl (head_symbolsq, wordq, ptl', head_symbolt,
           wordt, x)) ptlz))
  | Shift_ptd (tok, symbolsq, wordq, ptl, ptlz) ->
    Some
      (build_pt_dot_from_ptl init full_word ((A.Gram.T
        (A.Gram.token_term tok)) :: symbolsq) (app wordq (tok :: []))
        (A.GramDefs.Cons_ptl (symbolsq, wordq, ptl, (A.Gram.T
        (A.Gram.token_term tok)), (tok :: []), (A.GramDefs.Terminal_pt tok)))
        ptlz)

  (** val next_ptd_iter :
      A.initstate -> A.Gram.token list -> pt_dot -> int -> pt_dot option **)

  let rec next_ptd_iter init full_word ptd log_n_steps =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> next_ptd init full_word ptd)
      (fun log_n_steps0 ->
      match next_ptd_iter init full_word ptd log_n_steps0 with
      | Some ptd0 -> next_ptd_iter init full_word ptd0 log_n_steps0
      | None -> None)
      log_n_steps

  (** val ptlz_cost :
      A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
      list -> ptl_zipper -> int **)

  let ptlz_cost _ _ =
    let rec ptlz_cost0 _ _ = function
    | Non_terminal_pt_ptlz (p, word, ptz) ->
      ptz_cost0 (A.Gram.NT (A.Gram.prod_lhs p)) word ptz
    | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, pt, ptlz') ->
      add (A.GramDefs.pt_size head_symbolt wordt pt)
        (ptlz_cost0 (head_symbolt :: head_symbolsq) (app wordq wordt) ptlz')
    and ptz_cost0 _ _ = function
    | Top_ptz -> 0
    | Cons_ptl_ptz (head_symbolsq, wordq, _, head_symbolt, wordt, ptlz') ->
      add (Stdlib.Int.succ 0)
        (ptlz_cost0 (head_symbolt :: head_symbolsq) (app wordq wordt) ptlz')
    in ptlz_cost0

  (** val ptz_cost :
      A.initstate -> A.Gram.token list -> A.Gram.symbol -> A.Gram.token list
      -> pt_zipper -> int **)

  let ptz_cost _ _ =
    let rec ptlz_cost0 _ _ = function
    | Non_terminal_pt_ptlz (p, word, ptz) ->
      ptz_cost0 (A.Gram.NT (A.Gram.prod_lhs p)) word ptz
    | Cons_ptl_ptlz (head_symbolsq, wordq, head_symbolt, wordt, pt, ptlz') ->
      add (A.GramDefs.pt_size head_symbolt wordt pt)
        (ptlz_cost0 (head_symbolt :: head_symbolsq) (app wordq wordt) ptlz')
    and ptz_cost0 _ _ = function
    | Top_ptz -> 0
    | Cons_ptl_ptz (head_symbolsq, wordq, _, head_symbolt, wordt, ptlz') ->
      add (Stdlib.Int.succ 0)
        (ptlz_cost0 (head_symbolt :: head_symbolsq) (app wordq wordt) ptlz')
    in ptz_cost0

  (** val ptd_cost : A.initstate -> A.Gram.token list -> pt_dot -> int **)

  let ptd_cost init full_word = function
  | Reduce_ptd (prod0, word, _, ptz) ->
    ptz_cost init full_word (A.Gram.NT (A.Gram.prod_lhs prod0)) word ptz
  | Shift_ptd (tok, symbolsq, wordq, _, ptlz) ->
    add (Stdlib.Int.succ 0)
      (ptlz_cost init full_word ((A.Gram.T
        (A.Gram.token_term tok)) :: symbolsq) (app wordq (tok :: [])) ptlz)
 end

module Coq5_Make =
 functor (Aut:Coq_T) ->
 struct
  module Inter = Coq1_Make(Aut)

  module Correct = Coq2_Make(Aut)(Inter)

  module Complete = Coq4_Make(Aut)(Inter)

  (** val complete_validator : unit -> bool **)

  let complete_validator =
    Complete.Valid.is_complete

  (** val safe_validator : unit -> bool **)

  let safe_validator =
    Inter.ValidSafe.is_safe

  (** val parse :
      Aut.initstate -> int -> Inter.buffer -> Aut.Gram.symbol_semantic_type
      Inter.parse_result **)

  let parse init log_n_steps buffer0 =
    Inter.parse init buffer0 log_n_steps
 end

module Cst =
 struct
  type obj =
  | TType of int
  | Nat
  | Zero
  | Succ of obj
  | App of obj * obj
  | Fun of char list * obj * obj
  | Pi of char list * obj * obj
  | Var of char list
 end

type token0 =
| ZERO of unit
| VAR of char list
| TYPE of unit
| SUCC of unit
| RPAREN of unit
| PI of unit
| NAT of unit
| LPAREN of unit
| LAMBDA of unit
| INT of int
| EOF of unit
| DOT of unit
| COLON of unit

module Gram =
 struct
  type terminal' =
  | COLON't
  | DOT't
  | EOF't
  | INT't
  | LAMBDA't
  | LPAREN't
  | NAT't
  | PI't
  | RPAREN't
  | SUCC't
  | TYPE't
  | VAR't
  | ZERO't

  type terminal = terminal'

  (** val terminalNum : terminal numbered **)

  let terminalNum =
    { inj = (fun x ->
      match x with
      | COLON't -> XH
      | DOT't -> XO XH
      | EOF't -> XI XH
      | INT't -> XO (XO XH)
      | LAMBDA't -> XI (XO XH)
      | LPAREN't -> XO (XI XH)
      | NAT't -> XI (XI XH)
      | PI't -> XO (XO (XO XH))
      | RPAREN't -> XI (XO (XO XH))
      | SUCC't -> XO (XI (XO XH))
      | TYPE't -> XI (XI (XO XH))
      | VAR't -> XO (XO (XI XH))
      | ZERO't -> XI (XO (XI XH))); surj = (fun n0 ->
      match n0 with
      | XI p ->
        (match p with
         | XI p0 ->
           (match p0 with
            | XI _ -> COLON't
            | XO p1 -> (match p1 with
                        | XH -> TYPE't
                        | _ -> COLON't)
            | XH -> NAT't)
         | XO p0 ->
           (match p0 with
            | XI p1 -> (match p1 with
                        | XH -> ZERO't
                        | _ -> COLON't)
            | XO p1 -> (match p1 with
                        | XH -> RPAREN't
                        | _ -> COLON't)
            | XH -> LAMBDA't)
         | XH -> EOF't)
      | XO p ->
        (match p with
         | XI p0 ->
           (match p0 with
            | XI _ -> COLON't
            | XO p1 -> (match p1 with
                        | XH -> SUCC't
                        | _ -> COLON't)
            | XH -> LPAREN't)
         | XO p0 ->
           (match p0 with
            | XI p1 -> (match p1 with
                        | XH -> VAR't
                        | _ -> COLON't)
            | XO p1 -> (match p1 with
                        | XH -> PI't
                        | _ -> COLON't)
            | XH -> INT't)
         | XH -> DOT't)
      | XH -> COLON't); inj_bound = (XI (XO (XI XH))) }

  (** val coq_TerminalAlph : terminal alphabet **)

  let coq_TerminalAlph =
    numberedAlphabet terminalNum

  type nonterminal' =
  | Coq_app_obj'nt
  | Coq_args_list'nt
  | Coq_args_obj'nt
  | Coq_obj'nt
  | Coq_prog'nt
  | Coq_simpl_obj'nt

  type nonterminal = nonterminal'

  (** val nonterminalNum : nonterminal numbered **)

  let nonterminalNum =
    { inj = (fun x ->
      match x with
      | Coq_app_obj'nt -> XH
      | Coq_args_list'nt -> XO XH
      | Coq_args_obj'nt -> XI XH
      | Coq_obj'nt -> XO (XO XH)
      | Coq_prog'nt -> XI (XO XH)
      | Coq_simpl_obj'nt -> XO (XI XH)); surj = (fun n0 ->
      match n0 with
      | XI p ->
        (match p with
         | XI _ -> Coq_app_obj'nt
         | XO p0 -> (match p0 with
                     | XH -> Coq_prog'nt
                     | _ -> Coq_app_obj'nt)
         | XH -> Coq_args_obj'nt)
      | XO p ->
        (match p with
         | XI p0 ->
           (match p0 with
            | XH -> Coq_simpl_obj'nt
            | _ -> Coq_app_obj'nt)
         | XO p0 -> (match p0 with
                     | XH -> Coq_obj'nt
                     | _ -> Coq_app_obj'nt)
         | XH -> Coq_args_list'nt)
      | XH -> Coq_app_obj'nt); inj_bound = (XO (XI XH)) }

  (** val coq_NonTerminalAlph : nonterminal alphabet **)

  let coq_NonTerminalAlph =
    numberedAlphabet nonterminalNum

  type symbol =
  | T of terminal
  | NT of nonterminal

  (** val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1 **)

  let symbol_rect f f0 = function
  | T t0 -> f t0
  | NT n0 -> f0 n0

  (** val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1 **)

  let symbol_rec f f0 = function
  | T t0 -> f t0
  | NT n0 -> f0 n0

  (** val coq_SymbolAlph : symbol alphabet **)

  let coq_SymbolAlph =
    { alphabetComparable = (fun x y ->
      match x with
      | T x0 ->
        (match y with
         | T y0 -> compare1 coq_TerminalAlph.alphabetComparable x0 y0
         | NT _ -> Gt)
      | NT x0 ->
        (match y with
         | T _ -> Lt
         | NT y0 -> compare1 coq_NonTerminalAlph.alphabetComparable x0 y0));
      alphabetFinite =
      (app (map (fun x -> T x) (all_list coq_TerminalAlph.alphabetFinite))
        (map (fun x -> NT x) (all_list coq_NonTerminalAlph.alphabetFinite))) }

  type terminal_semantic_type = __

  type nonterminal_semantic_type = __

  type symbol_semantic_type = __

  type token = token0

  (** val token_term : token -> terminal **)

  let token_term = function
  | ZERO _ -> ZERO't
  | VAR _ -> VAR't
  | TYPE _ -> TYPE't
  | SUCC _ -> SUCC't
  | RPAREN _ -> RPAREN't
  | PI _ -> PI't
  | NAT _ -> NAT't
  | LPAREN _ -> LPAREN't
  | LAMBDA _ -> LAMBDA't
  | INT _ -> INT't
  | EOF _ -> EOF't
  | DOT _ -> DOT't
  | COLON _ -> COLON't

  (** val token_sem : token -> symbol_semantic_type **)

  let token_sem = function
  | ZERO x -> Obj.magic x
  | VAR x -> Obj.magic x
  | TYPE x -> Obj.magic x
  | SUCC x -> Obj.magic x
  | RPAREN x -> Obj.magic x
  | PI x -> Obj.magic x
  | NAT x -> Obj.magic x
  | LPAREN x -> Obj.magic x
  | LAMBDA x -> Obj.magic x
  | INT x -> Obj.magic x
  | EOF x -> Obj.magic x
  | DOT x -> Obj.magic x
  | COLON x -> Obj.magic x

  type production' =
  | Prod'simpl_obj'1
  | Prod'simpl_obj'0
  | Prod'prog'0
  | Prod'obj'6
  | Prod'obj'5
  | Prod'obj'4
  | Prod'obj'3
  | Prod'obj'2
  | Prod'obj'1
  | Prod'obj'0
  | Prod'args_obj'0
  | Prod'args_list'1
  | Prod'args_list'0
  | Prod'app_obj'1
  | Prod'app_obj'0

  type production = production'

  (** val productionNum : production numbered **)

  let productionNum =
    { inj = (fun x ->
      match x with
      | Prod'simpl_obj'1 -> XH
      | Prod'simpl_obj'0 -> XO XH
      | Prod'prog'0 -> XI XH
      | Prod'obj'6 -> XO (XO XH)
      | Prod'obj'5 -> XI (XO XH)
      | Prod'obj'4 -> XO (XI XH)
      | Prod'obj'3 -> XI (XI XH)
      | Prod'obj'2 -> XO (XO (XO XH))
      | Prod'obj'1 -> XI (XO (XO XH))
      | Prod'obj'0 -> XO (XI (XO XH))
      | Prod'args_obj'0 -> XI (XI (XO XH))
      | Prod'args_list'1 -> XO (XO (XI XH))
      | Prod'args_list'0 -> XI (XO (XI XH))
      | Prod'app_obj'1 -> XO (XI (XI XH))
      | Prod'app_obj'0 -> XI (XI (XI XH))); surj = (fun n0 ->
      match n0 with
      | XI p ->
        (match p with
         | XI p0 ->
           (match p0 with
            | XI p1 ->
              (match p1 with
               | XH -> Prod'app_obj'0
               | _ -> Prod'simpl_obj'1)
            | XO p1 ->
              (match p1 with
               | XH -> Prod'args_obj'0
               | _ -> Prod'simpl_obj'1)
            | XH -> Prod'obj'3)
         | XO p0 ->
           (match p0 with
            | XI p1 ->
              (match p1 with
               | XH -> Prod'args_list'0
               | _ -> Prod'simpl_obj'1)
            | XO p1 ->
              (match p1 with
               | XH -> Prod'obj'1
               | _ -> Prod'simpl_obj'1)
            | XH -> Prod'obj'5)
         | XH -> Prod'prog'0)
      | XO p ->
        (match p with
         | XI p0 ->
           (match p0 with
            | XI p1 ->
              (match p1 with
               | XH -> Prod'app_obj'1
               | _ -> Prod'simpl_obj'1)
            | XO p1 ->
              (match p1 with
               | XH -> Prod'obj'0
               | _ -> Prod'simpl_obj'1)
            | XH -> Prod'obj'4)
         | XO p0 ->
           (match p0 with
            | XI p1 ->
              (match p1 with
               | XH -> Prod'args_list'1
               | _ -> Prod'simpl_obj'1)
            | XO p1 ->
              (match p1 with
               | XH -> Prod'obj'2
               | _ -> Prod'simpl_obj'1)
            | XH -> Prod'obj'6)
         | XH -> Prod'simpl_obj'0)
      | XH -> Prod'simpl_obj'1); inj_bound = (XI (XI (XI XH))) }

  (** val coq_ProductionAlph : production alphabet **)

  let coq_ProductionAlph =
    numberedAlphabet productionNum

  (** val prod_contents :
      production -> (nonterminal * symbol list, symbol_semantic_type
      arrows_right) sigT **)

  let prod_contents p =
    let box = fun x x0 -> ExistT (x, x0) in
    (match p with
     | Prod'simpl_obj'1 ->
       Obj.magic box (Coq_simpl_obj'nt, ((T RPAREN't) :: ((NT
         Coq_obj'nt) :: ((T LPAREN't) :: [])))) (fun _ _4 _ -> _4)
     | Prod'simpl_obj'0 ->
       Obj.magic box (Coq_simpl_obj'nt, ((T VAR't) :: [])) (fun _4 -> Cst.Var
         _4)
     | Prod'prog'0 ->
       Obj.magic box (Coq_prog'nt, ((T EOF't) :: ((NT Coq_obj'nt) :: [])))
         (fun _ _4 -> _4)
     | Prod'obj'6 ->
       Obj.magic box (Coq_obj'nt, ((NT Coq_app_obj'nt) :: [])) (fun _4 -> _4)
     | Prod'obj'5 ->
       Obj.magic box (Coq_obj'nt, ((NT Coq_simpl_obj'nt) :: ((T
         SUCC't) :: []))) (fun _4 _ -> Cst.Succ _4)
     | Prod'obj'4 ->
       Obj.magic box (Coq_obj'nt, ((T INT't) :: ((T TYPE't) :: [])))
         (fun _4 _ -> Cst.TType _4)
     | Prod'obj'3 ->
       Obj.magic box (Coq_obj'nt, ((T ZERO't) :: [])) (fun _ -> Cst.Zero)
     | Prod'obj'2 ->
       Obj.magic box (Coq_obj'nt, ((T NAT't) :: [])) (fun _ -> Cst.Nat)
     | Prod'obj'1 ->
       Obj.magic box (Coq_obj'nt, ((NT Coq_obj'nt) :: ((T DOT't) :: ((NT
         Coq_args_list'nt) :: ((T PI't) :: []))))) (fun _4 _ _5 _ ->
         fold_left (fun acc arg -> Cst.Pi ((fst arg), (snd arg), acc)) _5 _4)
     | Prod'obj'0 ->
       Obj.magic box (Coq_obj'nt, ((NT Coq_obj'nt) :: ((T DOT't) :: ((NT
         Coq_args_list'nt) :: ((T LAMBDA't) :: []))))) (fun _4 _ _5 _ ->
         fold_left (fun acc arg -> Cst.Fun ((fst arg), (snd arg), acc)) _5 _4)
     | Prod'args_obj'0 ->
       Obj.magic box (Coq_args_obj'nt, ((T RPAREN't) :: ((NT
         Coq_obj'nt) :: ((T COLON't) :: ((T VAR't) :: ((T
         LPAREN't) :: [])))))) (fun _ _4 _ _5 _ -> (_5, _4))
     | Prod'args_list'1 ->
       Obj.magic box (Coq_args_list'nt, ((NT Coq_args_obj'nt) :: []))
         (fun _4 -> _4 :: [])
     | Prod'args_list'0 ->
       Obj.magic box (Coq_args_list'nt, ((NT Coq_args_obj'nt) :: ((NT
         Coq_args_list'nt) :: []))) (fun _4 _5 -> _4 :: _5)
     | Prod'app_obj'1 ->
       Obj.magic box (Coq_app_obj'nt, ((NT Coq_simpl_obj'nt) :: []))
         (fun _4 -> _4)
     | Prod'app_obj'0 ->
       Obj.magic box (Coq_app_obj'nt, ((NT Coq_simpl_obj'nt) :: ((NT
         Coq_app_obj'nt) :: []))) (fun _4 _5 -> Cst.App (_5, _4)))

  (** val prod_lhs : production -> nonterminal **)

  let prod_lhs p =
    fst (projT1 (prod_contents p))

  (** val prod_rhs_rev : production -> symbol list **)

  let prod_rhs_rev p =
    snd (projT1 (prod_contents p))

  (** val prod_action : production -> symbol_semantic_type arrows_right **)

  let prod_action p =
    projT2 (prod_contents p)

  type parse_tree =
  | Terminal_pt of token
  | Non_terminal_pt of production * token list * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of symbol list * token list * parse_tree_list * symbol
     * token list * parse_tree

  (** val parse_tree_rect :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1 **)

  let parse_tree_rect f f0 _ _ = function
  | Terminal_pt tok -> f tok
  | Non_terminal_pt (prod0, word, p0) -> f0 prod0 word p0

  (** val parse_tree_rec :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1 **)

  let parse_tree_rec f f0 _ _ = function
  | Terminal_pt tok -> f tok
  | Non_terminal_pt (prod0, word, p0) -> f0 prod0 word p0

  (** val parse_tree_list_rect :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1 **)

  let rec parse_tree_list_rect f f0 _ _ = function
  | Nil_ptl -> f
  | Cons_ptl (head_symbolsq, wordq, p0, head_symbolt, wordt, p1) ->
    f0 head_symbolsq wordq p0
      (parse_tree_list_rect f f0 head_symbolsq wordq p0) head_symbolt wordt p1

  (** val parse_tree_list_rec :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1 **)

  let rec parse_tree_list_rec f f0 _ _ = function
  | Nil_ptl -> f
  | Cons_ptl (head_symbolsq, wordq, p0, head_symbolt, wordt, p1) ->
    f0 head_symbolsq wordq p0
      (parse_tree_list_rec f f0 head_symbolsq wordq p0) head_symbolt wordt p1

  (** val pt_sem :
      symbol -> token list -> parse_tree -> symbol_semantic_type **)

  let rec pt_sem _ _ = function
  | Terminal_pt tok -> token_sem tok
  | Non_terminal_pt (prod0, word0, ptl) ->
    Obj.magic ptl_sem (prod_rhs_rev prod0) word0 ptl (prod_action prod0)

  (** val ptl_sem :
      symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1 **)

  and ptl_sem _ _ tree0 act =
    match tree0 with
    | Nil_ptl -> Obj.magic act
    | Cons_ptl (head_symbolsq, wordq, q, head_symbolt, wordt, t0) ->
      ptl_sem head_symbolsq wordq q
        (Obj.magic act (pt_sem head_symbolt wordt t0))

  (** val pt_size : symbol -> token list -> parse_tree -> int **)

  let rec pt_size _ _ = function
  | Terminal_pt _ -> Stdlib.Int.succ 0
  | Non_terminal_pt (prod0, word0, l) ->
    Stdlib.Int.succ (ptl_size (prod_rhs_rev prod0) word0 l)

  (** val ptl_size : symbol list -> token list -> parse_tree_list -> int **)

  and ptl_size _ _ = function
  | Nil_ptl -> 0
  | Cons_ptl (head_symbolsq, wordq, q, head_symbolt, wordt, t0) ->
    add (pt_size head_symbolt wordt t0) (ptl_size head_symbolsq wordq q)
 end
module Coq__1 = Gram

module Aut =
 struct
  module Gram = Gram

  module GramDefs = Gram

  (** val nullable_nterm : Coq__1.nonterminal -> bool **)

  let nullable_nterm _ =
    false

  (** val first_nterm : Coq__1.nonterminal -> Coq__1.terminal list **)

  let first_nterm = function
  | Coq__1.Coq_app_obj'nt -> Coq__1.VAR't :: (Coq__1.LPAREN't :: [])
  | Coq__1.Coq_args_list'nt -> Coq__1.LPAREN't :: []
  | Coq__1.Coq_args_obj'nt -> Coq__1.LPAREN't :: []
  | Coq__1.Coq_simpl_obj'nt -> Coq__1.VAR't :: (Coq__1.LPAREN't :: [])
  | _ ->
    Coq__1.ZERO't :: (Coq__1.VAR't :: (Coq__1.TYPE't :: (Coq__1.SUCC't :: (Coq__1.PI't :: (Coq__1.NAT't :: (Coq__1.LPAREN't :: (Coq__1.LAMBDA't :: [])))))))

  type noninitstate' =
  | Nis'31
  | Nis'30
  | Nis'28
  | Nis'27
  | Nis'26
  | Nis'25
  | Nis'24
  | Nis'23
  | Nis'22
  | Nis'21
  | Nis'20
  | Nis'19
  | Nis'18
  | Nis'17
  | Nis'16
  | Nis'15
  | Nis'14
  | Nis'13
  | Nis'12
  | Nis'11
  | Nis'10
  | Nis'9
  | Nis'8
  | Nis'7
  | Nis'6
  | Nis'5
  | Nis'4
  | Nis'3
  | Nis'2
  | Nis'1

  type noninitstate = noninitstate'

  (** val noninitstateNum : noninitstate numbered **)

  let noninitstateNum =
    { inj = (fun x ->
      match x with
      | Nis'31 -> XH
      | Nis'30 -> XO XH
      | Nis'28 -> XI XH
      | Nis'27 -> XO (XO XH)
      | Nis'26 -> XI (XO XH)
      | Nis'25 -> XO (XI XH)
      | Nis'24 -> XI (XI XH)
      | Nis'23 -> XO (XO (XO XH))
      | Nis'22 -> XI (XO (XO XH))
      | Nis'21 -> XO (XI (XO XH))
      | Nis'20 -> XI (XI (XO XH))
      | Nis'19 -> XO (XO (XI XH))
      | Nis'18 -> XI (XO (XI XH))
      | Nis'17 -> XO (XI (XI XH))
      | Nis'16 -> XI (XI (XI XH))
      | Nis'15 -> XO (XO (XO (XO XH)))
      | Nis'14 -> XI (XO (XO (XO XH)))
      | Nis'13 -> XO (XI (XO (XO XH)))
      | Nis'12 -> XI (XI (XO (XO XH)))
      | Nis'11 -> XO (XO (XI (XO XH)))
      | Nis'10 -> XI (XO (XI (XO XH)))
      | Nis'9 -> XO (XI (XI (XO XH)))
      | Nis'8 -> XI (XI (XI (XO XH)))
      | Nis'7 -> XO (XO (XO (XI XH)))
      | Nis'6 -> XI (XO (XO (XI XH)))
      | Nis'5 -> XO (XI (XO (XI XH)))
      | Nis'4 -> XI (XI (XO (XI XH)))
      | Nis'3 -> XO (XO (XI (XI XH)))
      | Nis'2 -> XI (XO (XI (XI XH)))
      | Nis'1 -> XO (XI (XI (XI XH)))); surj = (fun n0 ->
      match n0 with
      | XI p ->
        (match p with
         | XI p0 ->
           (match p0 with
            | XI p1 ->
              (match p1 with
               | XI _ -> Nis'31
               | XO p2 -> (match p2 with
                           | XH -> Nis'8
                           | _ -> Nis'31)
               | XH -> Nis'16)
            | XO p1 ->
              (match p1 with
               | XI p2 -> (match p2 with
                           | XH -> Nis'4
                           | _ -> Nis'31)
               | XO p2 -> (match p2 with
                           | XH -> Nis'12
                           | _ -> Nis'31)
               | XH -> Nis'20)
            | XH -> Nis'24)
         | XO p0 ->
           (match p0 with
            | XI p1 ->
              (match p1 with
               | XI p2 -> (match p2 with
                           | XH -> Nis'2
                           | _ -> Nis'31)
               | XO p2 -> (match p2 with
                           | XH -> Nis'10
                           | _ -> Nis'31)
               | XH -> Nis'18)
            | XO p1 ->
              (match p1 with
               | XI p2 -> (match p2 with
                           | XH -> Nis'6
                           | _ -> Nis'31)
               | XO p2 -> (match p2 with
                           | XH -> Nis'14
                           | _ -> Nis'31)
               | XH -> Nis'22)
            | XH -> Nis'26)
         | XH -> Nis'28)
      | XO p ->
        (match p with
         | XI p0 ->
           (match p0 with
            | XI p1 ->
              (match p1 with
               | XI p2 -> (match p2 with
                           | XH -> Nis'1
                           | _ -> Nis'31)
               | XO p2 -> (match p2 with
                           | XH -> Nis'9
                           | _ -> Nis'31)
               | XH -> Nis'17)
            | XO p1 ->
              (match p1 with
               | XI p2 -> (match p2 with
                           | XH -> Nis'5
                           | _ -> Nis'31)
               | XO p2 -> (match p2 with
                           | XH -> Nis'13
                           | _ -> Nis'31)
               | XH -> Nis'21)
            | XH -> Nis'25)
         | XO p0 ->
           (match p0 with
            | XI p1 ->
              (match p1 with
               | XI p2 -> (match p2 with
                           | XH -> Nis'3
                           | _ -> Nis'31)
               | XO p2 -> (match p2 with
                           | XH -> Nis'11
                           | _ -> Nis'31)
               | XH -> Nis'19)
            | XO p1 ->
              (match p1 with
               | XI p2 -> (match p2 with
                           | XH -> Nis'7
                           | _ -> Nis'31)
               | XO p2 -> (match p2 with
                           | XH -> Nis'15
                           | _ -> Nis'31)
               | XH -> Nis'23)
            | XH -> Nis'27)
         | XH -> Nis'30)
      | XH -> Nis'31); inj_bound = (XO (XI (XI (XI XH)))) }

  (** val coq_NonInitStateAlph : noninitstate alphabet **)

  let coq_NonInitStateAlph =
    numberedAlphabet noninitstateNum

  (** val last_symb_of_non_init_state : noninitstate -> Coq__1.symbol **)

  let last_symb_of_non_init_state = function
  | Nis'31 -> Coq__1.T Coq__1.EOF't
  | Nis'28 -> Coq__1.NT Coq__1.Coq_simpl_obj'nt
  | Nis'27 -> Coq__1.T Coq__1.RPAREN't
  | Nis'24 -> Coq__1.T Coq__1.DOT't
  | Nis'23 -> Coq__1.NT Coq__1.Coq_args_list'nt
  | Nis'22 -> Coq__1.T Coq__1.RPAREN't
  | Nis'20 -> Coq__1.NT Coq__1.Coq_args_obj'nt
  | Nis'19 -> Coq__1.NT Coq__1.Coq_simpl_obj'nt
  | Nis'18 -> Coq__1.NT Coq__1.Coq_app_obj'nt
  | Nis'16 -> Coq__1.NT Coq__1.Coq_simpl_obj'nt
  | Nis'15 -> Coq__1.T Coq__1.DOT't
  | Nis'14 -> Coq__1.NT Coq__1.Coq_args_list'nt
  | Nis'13 -> Coq__1.NT Coq__1.Coq_args_obj'nt
  | Nis'12 -> Coq__1.T Coq__1.LAMBDA't
  | Nis'11 -> Coq__1.T Coq__1.NAT't
  | Nis'10 -> Coq__1.T Coq__1.COLON't
  | Nis'9 -> Coq__1.T Coq__1.VAR't
  | Nis'8 -> Coq__1.T Coq__1.LPAREN't
  | Nis'7 -> Coq__1.T Coq__1.PI't
  | Nis'6 -> Coq__1.T Coq__1.LPAREN't
  | Nis'5 -> Coq__1.T Coq__1.SUCC't
  | Nis'4 -> Coq__1.T Coq__1.INT't
  | Nis'3 -> Coq__1.T Coq__1.TYPE't
  | Nis'2 -> Coq__1.T Coq__1.VAR't
  | Nis'1 -> Coq__1.T Coq__1.ZERO't
  | _ -> Coq__1.NT Coq__1.Coq_obj'nt

  type initstate' =
  | Init'0

  type initstate = initstate'

  (** val initstateNum : initstate numbered **)

  let initstateNum =
    { inj = (fun _ -> XH); surj = (fun _ -> Init'0); inj_bound = XH }

  (** val coq_InitStateAlph : initstate alphabet **)

  let coq_InitStateAlph =
    numberedAlphabet initstateNum

  type state =
  | Init of initstate
  | Ninit of noninitstate

  (** val state_rect :
      (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1 **)

  let state_rect f f0 = function
  | Init i -> f i
  | Ninit n0 -> f0 n0

  (** val state_rec :
      (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1 **)

  let state_rec f f0 = function
  | Init i -> f i
  | Ninit n0 -> f0 n0

  (** val coq_StateAlph : state alphabet **)

  let coq_StateAlph =
    { alphabetComparable = (fun x y ->
      match x with
      | Init x0 ->
        (match y with
         | Init y0 -> compare1 coq_InitStateAlph.alphabetComparable x0 y0
         | Ninit _ -> Lt)
      | Ninit x0 ->
        (match y with
         | Init _ -> Gt
         | Ninit y0 -> compare1 coq_NonInitStateAlph.alphabetComparable x0 y0));
      alphabetFinite =
      (app
        (map (fun x -> Init x) (all_list coq_InitStateAlph.alphabetFinite))
        (map (fun x -> Ninit x)
          (all_list coq_NonInitStateAlph.alphabetFinite))) }

  type lookahead_action =
  | Shift_act of noninitstate
  | Reduce_act of Gram.production
  | Fail_act

  (** val lookahead_action_rect :
      Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production ->
      'a1) -> 'a1 -> lookahead_action -> 'a1 **)

  let lookahead_action_rect _ f f0 f1 = function
  | Shift_act s -> f s __
  | Reduce_act p -> f0 p
  | Fail_act -> f1

  (** val lookahead_action_rec :
      Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production ->
      'a1) -> 'a1 -> lookahead_action -> 'a1 **)

  let lookahead_action_rec _ f f0 f1 = function
  | Shift_act s -> f s __
  | Reduce_act p -> f0 p
  | Fail_act -> f1

  type action =
  | Default_reduce_act of Gram.production
  | Lookahead_act of (Gram.terminal -> lookahead_action)

  (** val action_rect :
      (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) ->
      'a1) -> action -> 'a1 **)

  let action_rect f f0 = function
  | Default_reduce_act p -> f p
  | Lookahead_act l -> f0 l

  (** val action_rec :
      (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) ->
      'a1) -> action -> 'a1 **)

  let action_rec f f0 = function
  | Default_reduce_act p -> f p
  | Lookahead_act l -> f0 l

  type item = { prod_item : Gram.production; dot_pos_item : int;
                lookaheads_item : Gram.terminal list }

  (** val prod_item : item -> Gram.production **)

  let prod_item i =
    i.prod_item

  (** val dot_pos_item : item -> int **)

  let dot_pos_item i =
    i.dot_pos_item

  (** val lookaheads_item : item -> Gram.terminal list **)

  let lookaheads_item i =
    i.lookaheads_item

  (** val start_nt : initstate -> Coq__1.nonterminal **)

  let start_nt _ =
    Coq__1.Coq_prog'nt

  (** val action_table : state -> action **)

  let action_table = function
  | Init _ ->
    Lookahead_act (fun terminal0 ->
      match terminal0 with
      | Coq__1.LAMBDA't -> Shift_act Nis'12
      | Coq__1.LPAREN't -> Shift_act Nis'6
      | Coq__1.NAT't -> Shift_act Nis'11
      | Coq__1.PI't -> Shift_act Nis'7
      | Coq__1.SUCC't -> Shift_act Nis'5
      | Coq__1.TYPE't -> Shift_act Nis'3
      | Coq__1.VAR't -> Shift_act Nis'2
      | Coq__1.ZERO't -> Shift_act Nis'1
      | _ -> Fail_act)
  | Ninit n0 ->
    (match n0 with
     | Nis'31 -> Default_reduce_act Coq__1.Prod'prog'0
     | Nis'30 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.EOF't -> Shift_act Nis'31
         | _ -> Fail_act)
     | Nis'28 -> Default_reduce_act Coq__1.Prod'obj'5
     | Nis'27 -> Default_reduce_act Coq__1.Prod'simpl_obj'1
     | Nis'26 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN't -> Shift_act Nis'27
         | _ -> Fail_act)
     | Nis'25 -> Default_reduce_act Coq__1.Prod'obj'1
     | Nis'23 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.DOT't -> Shift_act Nis'24
         | Coq__1.LPAREN't -> Shift_act Nis'8
         | _ -> Fail_act)
     | Nis'22 -> Default_reduce_act Coq__1.Prod'args_obj'0
     | Nis'21 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN't -> Shift_act Nis'22
         | _ -> Fail_act)
     | Nis'20 -> Default_reduce_act Coq__1.Prod'args_list'0
     | Nis'19 -> Default_reduce_act Coq__1.Prod'app_obj'0
     | Nis'18 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.EOF't -> Reduce_act Coq__1.Prod'obj'6
         | Coq__1.LPAREN't -> Shift_act Nis'6
         | Coq__1.RPAREN't -> Reduce_act Coq__1.Prod'obj'6
         | Coq__1.VAR't -> Shift_act Nis'2
         | _ -> Fail_act)
     | Nis'17 -> Default_reduce_act Coq__1.Prod'obj'0
     | Nis'16 -> Default_reduce_act Coq__1.Prod'app_obj'1
     | Nis'14 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.DOT't -> Shift_act Nis'15
         | Coq__1.LPAREN't -> Shift_act Nis'8
         | _ -> Fail_act)
     | Nis'13 -> Default_reduce_act Coq__1.Prod'args_list'1
     | Nis'12 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN't -> Shift_act Nis'8
         | _ -> Fail_act)
     | Nis'11 -> Default_reduce_act Coq__1.Prod'obj'2
     | Nis'9 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON't -> Shift_act Nis'10
         | _ -> Fail_act)
     | Nis'8 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.VAR't -> Shift_act Nis'9
         | _ -> Fail_act)
     | Nis'7 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN't -> Shift_act Nis'8
         | _ -> Fail_act)
     | Nis'5 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN't -> Shift_act Nis'6
         | Coq__1.VAR't -> Shift_act Nis'2
         | _ -> Fail_act)
     | Nis'4 -> Default_reduce_act Coq__1.Prod'obj'4
     | Nis'3 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.INT't -> Shift_act Nis'4
         | _ -> Fail_act)
     | Nis'2 -> Default_reduce_act Coq__1.Prod'simpl_obj'0
     | Nis'1 -> Default_reduce_act Coq__1.Prod'obj'3
     | _ ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__1.LAMBDA't -> Shift_act Nis'12
         | Coq__1.LPAREN't -> Shift_act Nis'6
         | Coq__1.NAT't -> Shift_act Nis'11
         | Coq__1.PI't -> Shift_act Nis'7
         | Coq__1.SUCC't -> Shift_act Nis'5
         | Coq__1.TYPE't -> Shift_act Nis'3
         | Coq__1.VAR't -> Shift_act Nis'2
         | Coq__1.ZERO't -> Shift_act Nis'1
         | _ -> Fail_act))

  (** val goto_table : state -> Coq__1.nonterminal -> noninitstate option **)

  let goto_table state0 nt =
    match state0 with
    | Init _ ->
      (match nt with
       | Coq__1.Coq_app_obj'nt -> Some Nis'18
       | Coq__1.Coq_obj'nt -> Some Nis'30
       | Coq__1.Coq_simpl_obj'nt -> Some Nis'16
       | _ -> None)
    | Ninit n0 ->
      (match n0 with
       | Nis'24 ->
         (match nt with
          | Coq__1.Coq_app_obj'nt -> Some Nis'18
          | Coq__1.Coq_obj'nt -> Some Nis'25
          | Coq__1.Coq_simpl_obj'nt -> Some Nis'16
          | _ -> None)
       | Nis'23 ->
         (match nt with
          | Coq__1.Coq_args_obj'nt -> Some Nis'20
          | _ -> None)
       | Nis'18 ->
         (match nt with
          | Coq__1.Coq_simpl_obj'nt -> Some Nis'19
          | _ -> None)
       | Nis'15 ->
         (match nt with
          | Coq__1.Coq_app_obj'nt -> Some Nis'18
          | Coq__1.Coq_obj'nt -> Some Nis'17
          | Coq__1.Coq_simpl_obj'nt -> Some Nis'16
          | _ -> None)
       | Nis'14 ->
         (match nt with
          | Coq__1.Coq_args_obj'nt -> Some Nis'20
          | _ -> None)
       | Nis'12 ->
         (match nt with
          | Coq__1.Coq_args_list'nt -> Some Nis'14
          | Coq__1.Coq_args_obj'nt -> Some Nis'13
          | _ -> None)
       | Nis'10 ->
         (match nt with
          | Coq__1.Coq_app_obj'nt -> Some Nis'18
          | Coq__1.Coq_obj'nt -> Some Nis'21
          | Coq__1.Coq_simpl_obj'nt -> Some Nis'16
          | _ -> None)
       | Nis'7 ->
         (match nt with
          | Coq__1.Coq_args_list'nt -> Some Nis'23
          | Coq__1.Coq_args_obj'nt -> Some Nis'13
          | _ -> None)
       | Nis'6 ->
         (match nt with
          | Coq__1.Coq_app_obj'nt -> Some Nis'18
          | Coq__1.Coq_obj'nt -> Some Nis'26
          | Coq__1.Coq_simpl_obj'nt -> Some Nis'16
          | _ -> None)
       | Nis'5 ->
         (match nt with
          | Coq__1.Coq_simpl_obj'nt -> Some Nis'28
          | _ -> None)
       | _ -> None)

  (** val past_symb_of_non_init_state : noninitstate -> Coq__1.symbol list **)

  let past_symb_of_non_init_state = fun _ -> assert false

  (** val past_state_of_non_init_state :
      noninitstate -> (state -> bool) list **)

  let past_state_of_non_init_state = fun _ -> assert false

  (** val items_of_state : state -> item list **)

  let items_of_state = fun _ -> assert false

  (** val coq_N_of_state : state -> n **)

  let coq_N_of_state = function
  | Init _ -> N0
  | Ninit n0 ->
    (match n0 with
     | Nis'31 -> Npos (XI (XI (XI (XI XH))))
     | Nis'30 -> Npos (XO (XI (XI (XI XH))))
     | Nis'28 -> Npos (XO (XO (XI (XI XH))))
     | Nis'27 -> Npos (XI (XI (XO (XI XH))))
     | Nis'26 -> Npos (XO (XI (XO (XI XH))))
     | Nis'25 -> Npos (XI (XO (XO (XI XH))))
     | Nis'24 -> Npos (XO (XO (XO (XI XH))))
     | Nis'23 -> Npos (XI (XI (XI (XO XH))))
     | Nis'22 -> Npos (XO (XI (XI (XO XH))))
     | Nis'21 -> Npos (XI (XO (XI (XO XH))))
     | Nis'20 -> Npos (XO (XO (XI (XO XH))))
     | Nis'19 -> Npos (XI (XI (XO (XO XH))))
     | Nis'18 -> Npos (XO (XI (XO (XO XH))))
     | Nis'17 -> Npos (XI (XO (XO (XO XH))))
     | Nis'16 -> Npos (XO (XO (XO (XO XH))))
     | Nis'15 -> Npos (XI (XI (XI XH)))
     | Nis'14 -> Npos (XO (XI (XI XH)))
     | Nis'13 -> Npos (XI (XO (XI XH)))
     | Nis'12 -> Npos (XO (XO (XI XH)))
     | Nis'11 -> Npos (XI (XI (XO XH)))
     | Nis'10 -> Npos (XO (XI (XO XH)))
     | Nis'9 -> Npos (XI (XO (XO XH)))
     | Nis'8 -> Npos (XO (XO (XO XH)))
     | Nis'7 -> Npos (XI (XI XH))
     | Nis'6 -> Npos (XO (XI XH))
     | Nis'5 -> Npos (XI (XO XH))
     | Nis'4 -> Npos (XO (XO XH))
     | Nis'3 -> Npos (XI XH)
     | Nis'2 -> Npos (XO XH)
     | Nis'1 -> Npos XH)
 end

module MenhirLibParser = Coq5_Make(Aut)

(** val prog :
    int -> MenhirLibParser.Inter.buffer -> Cst.obj
    MenhirLibParser.Inter.parse_result **)

let prog =
  Obj.magic MenhirLibParser.parse Aut.Init'0
