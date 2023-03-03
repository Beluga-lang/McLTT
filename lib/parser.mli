
type __ = Obj.t

val implb : bool -> bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2



val add : int -> int -> int



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

module OT_to_Full :
 functor (O:OrderedType') ->
 sig
  type t = O.t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module OT_to_OrderTac :
 functor (OT:OrderedType) ->
 sig
  module OTF :
   sig
    type t = OT.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  module TO :
   sig
    type t = OTF.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end
 end

module OrderedTypeFacts :
 functor (O:OrderedType') ->
 sig
  module OrderTac :
   sig
    module OTF :
     sig
      type t = O.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> bool
     end

    module TO :
     sig
      type t = OTF.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> bool
     end
   end

  val eq_dec : O.t -> O.t -> bool

  val lt_dec : O.t -> O.t -> bool

  val eqb : O.t -> O.t -> bool
 end

module Nat :
 sig
  val compare : int -> int -> comparison
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

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val eq_dec : positive -> positive -> bool
 end

val rev : 'a1 list -> 'a1 list

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val rev' : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val eq_dec : z -> z -> bool
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

module Coq_OrderedTypeFacts :
 functor (O:Coq_OrderedType) ->
 sig
  module TO :
   sig
    type t = O.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : O.t -> O.t -> bool

  val lt_dec : O.t -> O.t -> bool

  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType :
 functor (O:Coq_OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> bool

    val lt_dec : O.t -> O.t -> bool

    val eqb : O.t -> O.t -> bool
   end
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

module Z_as_Int :
 sig
  type t = z

  val _0 : z

  val _1 : z

  val _2 : z

  val _3 : z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val max : z -> z -> z

  val eqb : z -> z -> bool

  val ltb : z -> z -> bool

  val leb : z -> z -> bool

  val eq_dec : z -> z -> bool

  val gt_le_dec : z -> z -> bool

  val ge_lt_dec : z -> z -> bool

  val i2z : t -> z
 end

module MakeListOrdering :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = O.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> bool
       end

      module TO :
       sig
        type t = OTF.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> bool
       end
     end

    val eq_dec : O.t -> O.t -> bool

    val lt_dec : O.t -> O.t -> bool

    val eqb : O.t -> O.t -> bool
   end
 end

module MakeRaw :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  type elt = X.t

  type tree =
  | Leaf
  | Node of I.t * tree * X.t * tree

  val empty : tree

  val is_empty : tree -> bool

  val mem : X.t -> tree -> bool

  val min_elt : tree -> elt option

  val max_elt : tree -> elt option

  val choose : tree -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

  val elements_aux : X.t list -> tree -> X.t list

  val elements : tree -> X.t list

  val rev_elements_aux : X.t list -> tree -> X.t list

  val rev_elements : tree -> X.t list

  val cardinal : tree -> int

  val maxdepth : tree -> int

  val mindepth : tree -> int

  val for_all : (elt -> bool) -> tree -> bool

  val exists_ : (elt -> bool) -> tree -> bool

  type enumeration =
  | End
  | More of elt * tree * enumeration

  val cons : tree -> enumeration -> enumeration

  val compare_more :
    X.t -> (enumeration -> comparison) -> enumeration -> comparison

  val compare_cont :
    tree -> (enumeration -> comparison) -> enumeration -> comparison

  val compare_end : enumeration -> comparison

  val compare : tree -> tree -> comparison

  val equal : tree -> tree -> bool

  val subsetl : (tree -> bool) -> X.t -> tree -> bool

  val subsetr : (tree -> bool) -> X.t -> tree -> bool

  val subset : tree -> tree -> bool

  type t = tree

  val height : t -> I.t

  val singleton : X.t -> tree

  val create : t -> X.t -> t -> tree

  val assert_false : t -> X.t -> t -> tree

  val bal : t -> X.t -> t -> tree

  val add : X.t -> tree -> tree

  val join : tree -> elt -> t -> t

  val remove_min : tree -> elt -> t -> t * elt

  val merge : tree -> tree -> tree

  val remove : X.t -> tree -> tree

  val concat : tree -> tree -> tree

  type triple = { t_left : t; t_in : bool; t_right : t }

  val t_left : triple -> t

  val t_in : triple -> bool

  val t_right : triple -> t

  val split : X.t -> tree -> triple

  val inter : tree -> tree -> tree

  val diff : tree -> tree -> tree

  val union : tree -> tree -> tree

  val filter : (elt -> bool) -> tree -> tree

  val partition : (elt -> bool) -> t -> t * t

  val ltb_tree : X.t -> tree -> bool

  val gtb_tree : X.t -> tree -> bool

  val isok : tree -> bool

  module MX :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = X.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> bool
       end

      module TO :
       sig
        type t = OTF.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> bool
       end
     end

    val eq_dec : X.t -> X.t -> bool

    val lt_dec : X.t -> X.t -> bool

    val eqb : X.t -> X.t -> bool
   end

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

  module L :
   sig
    module MO :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> bool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> bool
         end
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end
   end

  val flatten_e : enumeration -> elt list

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

module IntMake :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  module Raw :
   sig
    type elt = X.t

    type tree =
    | Leaf
    | Node of I.t * tree * X.t * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : X.t -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : X.t list -> tree -> X.t list

    val elements : tree -> X.t list

    val rev_elements_aux : X.t list -> tree -> X.t list

    val rev_elements : tree -> X.t list

    val cardinal : tree -> int

    val maxdepth : tree -> int

    val mindepth : tree -> int

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> X.t -> tree -> bool

    val subsetr : (tree -> bool) -> X.t -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> I.t

    val singleton : X.t -> tree

    val create : t -> X.t -> t -> tree

    val assert_false : t -> X.t -> t -> tree

    val bal : t -> X.t -> t -> tree

    val add : X.t -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> t * elt

    val merge : tree -> tree -> tree

    val remove : X.t -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : X.t -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> t * t

    val ltb_tree : X.t -> tree -> bool

    val gtb_tree : X.t -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> bool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> bool
         end
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

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

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> bool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> bool
           end
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * X.t * t
    | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
    | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
    | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree
    | R_bal_4 of t * X.t * t
    | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
    | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
    | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * 
       X.t * tree
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

  module E :
   sig
    type t = X.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> int

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module type OrderedTypeOrig =
 Coq_OrderedType

module Update_OT :
 functor (O:OrderedTypeOrig) ->
 sig
  type t = O.t

  val eq_dec : t -> t -> bool

  val compare : O.t -> O.t -> comparison
 end

module Coq_IntMake :
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 sig
  module X' :
   sig
    type t = X.t

    val eq_dec : t -> t -> bool

    val compare : X.t -> X.t -> comparison
   end

  module MSet :
   sig
    module Raw :
     sig
      type elt = X.t

      type tree =
      | Leaf
      | Node of I.t * tree * X.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : X.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : X.t list -> tree -> X.t list

      val elements : tree -> X.t list

      val rev_elements_aux : X.t list -> tree -> X.t list

      val rev_elements : tree -> X.t list

      val cardinal : tree -> int

      val maxdepth : tree -> int

      val mindepth : tree -> int

      val for_all : (elt -> bool) -> tree -> bool

      val exists_ : (elt -> bool) -> tree -> bool

      type enumeration =
      | End
      | More of elt * tree * enumeration

      val cons : tree -> enumeration -> enumeration

      val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> X.t -> tree -> bool

      val subsetr : (tree -> bool) -> X.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> I.t

      val singleton : X.t -> tree

      val create : t -> X.t -> t -> tree

      val assert_false : t -> X.t -> t -> tree

      val bal : t -> X.t -> t -> tree

      val add : X.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> t * elt

      val merge : tree -> tree -> tree

      val remove : X.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : X.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> t * t

      val ltb_tree : X.t -> tree -> bool

      val gtb_tree : X.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : X.t -> X.t -> comparison

            val eq_dec : X.t -> X.t -> bool
           end

          module TO :
           sig
            type t = X.t

            val compare : X.t -> X.t -> comparison

            val eq_dec : X.t -> X.t -> bool
           end
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * I.t * tree * X.t * tree
      | R_min_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * elt option * coq_R_min_elt

      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * I.t * tree * X.t * tree
      | R_max_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * elt option * coq_R_max_elt

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = X.t

              val compare : X.t -> X.t -> comparison

              val eq_dec : X.t -> X.t -> bool
             end

            module TO :
             sig
              type t = X.t

              val compare : X.t -> X.t -> comparison

              val eq_dec : X.t -> X.t -> bool
             end
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * X.t * t
      | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
      | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
      | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree
      | R_bal_4 of t * X.t * t
      | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
      | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
      | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree
      | R_bal_8 of t * X.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * I.t * tree * X.t * tree
         * (t * elt) * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * I.t * tree * X.t * tree
      | R_merge_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
         X.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * I.t * tree * X.t * tree
      | R_concat_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree
         * X.t * tree * t * elt

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

    module E :
     sig
      type t = X.t

      val compare : X.t -> X.t -> comparison

      val eq_dec : X.t -> X.t -> bool
     end

    type elt = X.t

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> int

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val eq_dec : t -> t -> bool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  type elt = X.t

  type t = MSet.t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val eq_dec : t -> t -> bool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> int

  val elements : t -> elt list

  val choose : t -> elt option

  module MF :
   sig
    val eqb : X.t -> X.t -> bool
   end

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val compare : t -> t -> t compare0

  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end
 end

module Make :
 functor (X:Coq_OrderedType) ->
 sig
  module X' :
   sig
    type t = X.t

    val eq_dec : t -> t -> bool

    val compare : X.t -> X.t -> comparison
   end

  module MSet :
   sig
    module Raw :
     sig
      type elt = X.t

      type tree =
      | Leaf
      | Node of Z_as_Int.t * tree * X.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : X.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : X.t list -> tree -> X.t list

      val elements : tree -> X.t list

      val rev_elements_aux : X.t list -> tree -> X.t list

      val rev_elements : tree -> X.t list

      val cardinal : tree -> int

      val maxdepth : tree -> int

      val mindepth : tree -> int

      val for_all : (elt -> bool) -> tree -> bool

      val exists_ : (elt -> bool) -> tree -> bool

      type enumeration =
      | End
      | More of elt * tree * enumeration

      val cons : tree -> enumeration -> enumeration

      val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> X.t -> tree -> bool

      val subsetr : (tree -> bool) -> X.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Z_as_Int.t

      val singleton : X.t -> tree

      val create : t -> X.t -> t -> tree

      val assert_false : t -> X.t -> t -> tree

      val bal : t -> X.t -> t -> tree

      val add : X.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> t * elt

      val merge : tree -> tree -> tree

      val remove : X.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : X.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> t * t

      val ltb_tree : X.t -> tree -> bool

      val gtb_tree : X.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : X.t -> X.t -> comparison

            val eq_dec : X.t -> X.t -> bool
           end

          module TO :
           sig
            type t = X.t

            val compare : X.t -> X.t -> comparison

            val eq_dec : X.t -> X.t -> bool
           end
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * Z_as_Int.t * tree * X.t * tree
      | R_min_elt_2 of tree * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree * elt option * coq_R_min_elt

      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * Z_as_Int.t * tree * X.t * tree
      | R_max_elt_2 of tree * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree * elt option * coq_R_max_elt

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = X.t

              val compare : X.t -> X.t -> comparison

              val eq_dec : X.t -> X.t -> bool
             end

            module TO :
             sig
              type t = X.t

              val compare : X.t -> X.t -> comparison

              val eq_dec : X.t -> X.t -> bool
             end
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * X.t * t
      | R_bal_1 of t * X.t * t * Z_as_Int.t * tree * X.t * tree
      | R_bal_2 of t * X.t * t * Z_as_Int.t * tree * X.t * tree
      | R_bal_3 of t * X.t * t * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree
      | R_bal_4 of t * X.t * t
      | R_bal_5 of t * X.t * t * Z_as_Int.t * tree * X.t * tree
      | R_bal_6 of t * X.t * t * Z_as_Int.t * tree * X.t * tree
      | R_bal_7 of t * X.t * t * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree
      | R_bal_8 of t * X.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * X.t * 
         tree * (t * elt) * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_merge_2 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_concat_2 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_inter_2 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * bool * t * tree * coq_R_inter
         * tree * coq_R_inter
      | R_inter_3 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * bool * t * tree * coq_R_inter
         * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_diff_2 of tree * tree * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree * t * bool * t * tree * coq_R_diff * tree
         * coq_R_diff
      | R_diff_3 of tree * tree * Z_as_Int.t * tree * X.t * tree * Z_as_Int.t
         * tree * X.t * tree * t * bool * t * tree * coq_R_diff * tree
         * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Z_as_Int.t * tree * X.t * tree
      | R_union_2 of tree * tree * Z_as_Int.t * tree * X.t * tree
         * Z_as_Int.t * tree * X.t * tree * t * bool * t * tree * coq_R_union
         * tree * coq_R_union
     end

    module E :
     sig
      type t = X.t

      val compare : X.t -> X.t -> comparison

      val eq_dec : X.t -> X.t -> bool
     end

    type elt = X.t

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> int

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val eq_dec : t -> t -> bool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  type elt = X.t

  type t = MSet.t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val eq_dec : t -> t -> bool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> int

  val elements : t -> elt list

  val choose : t -> elt option

  module MF :
   sig
    val eqb : X.t -> X.t -> bool
   end

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val compare : t -> t -> t compare0

  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end
 end

module Raw :
 functor (X:Coq_OrderedType) ->
 sig
  module MX :
   sig
    module TO :
     sig
      type t = X.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : X.t -> X.t -> bool

    val lt_dec : X.t -> X.t -> bool

    val eqb : X.t -> X.t -> bool
   end

  module PX :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end
   end

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val mem : key -> 'a1 t -> bool

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  val coq_R_mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
    'a1 coq_R_mem -> 'a2

  val coq_R_mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
    'a1 coq_R_mem -> 'a2

  val mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

  val find : key -> 'a1 t -> 'a1 option

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  val coq_R_find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
    'a1 option -> 'a1 coq_R_find -> 'a2

  val coq_R_find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
    'a1 option -> 'a1 coq_R_find -> 'a2

  val find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  val coq_R_add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
    -> 'a1 t -> 'a1 coq_R_add -> 'a2

  val coq_R_add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
    -> 'a1 t -> 'a1 coq_R_add -> 'a2

  val add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

  val remove : key -> 'a1 t -> 'a1 t

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  val coq_R_remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
    -> 'a1 coq_R_remove -> 'a2

  val coq_R_remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
    -> 'a1 coq_R_remove -> 'a2

  val remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

  val elements : 'a1 t -> 'a1 t

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  val coq_R_fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
    coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold
    -> 'a3

  val coq_R_fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
    coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold
    -> 'a3

  val fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
    'a2 -> 'a3

  val fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
    'a2 -> 'a3

  val coq_R_fold_correct :
    (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  val coq_R_equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t ->
    'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
    t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
    -> bool -> 'a1 coq_R_equal -> 'a2

  val coq_R_equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t ->
    'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
    t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
    -> bool -> 'a1 coq_R_equal -> 'a2

  val equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __
    -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

  val equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __
    -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

  val coq_R_equal_correct :
    ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

  val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

  val fold_right_pair :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

  val map2_alt :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3)
    list

  val at_least_one :
    'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option
 end

module Coq_Raw :
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 sig
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val height : 'a1 tree -> I.t

  val cardinal : 'a1 tree -> int

  val empty : 'a1 tree

  val is_empty : 'a1 tree -> bool

  val mem : X.t -> 'a1 tree -> bool

  val find : X.t -> 'a1 tree -> 'a1 option

  val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

  val remove_min :
    'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

  val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

  val remove : X.t -> 'a1 tree -> 'a1 tree

  val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  val t_left : 'a1 triple -> 'a1 tree

  val t_opt : 'a1 triple -> 'a1 option

  val t_right : 'a1 triple -> 'a1 tree

  val split : X.t -> 'a1 tree -> 'a1 triple

  val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

  val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

  val elements : 'a1 tree -> (key * 'a1) list

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  val enumeration_rect :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val enumeration_rec :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

  val equal_more :
    ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_cont :
    ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_end : 'a1 enumeration -> bool

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

  val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

  val map2_opt :
    (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
    ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
    tree

  module Proofs :
   sig
    module MX :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

    module PX :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end

    module L :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      type key = X.t

      type 'elt t = (X.t * 'elt) list

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val mem : key -> 'a1 t -> bool

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt t
      | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
         * 'elt coq_R_mem

      val coq_R_mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
        t -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
        t -> bool -> 'a1 coq_R_mem -> 'a2

      val mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

      val find : key -> 'a1 t -> 'a1 option

      type 'elt coq_R_find =
      | R_find_0 of 'elt t
      | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
         * 'elt coq_R_find

      val coq_R_find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
        -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
        -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      type 'elt coq_R_add =
      | R_add_0 of 'elt t
      | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
         * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
        -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
        -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

      val add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

      val remove : key -> 'a1 t -> 'a1 t

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt t
      | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
         * 'elt coq_R_remove

      val coq_R_remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
        'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
        'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

      val remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

      val elements : 'a1 t -> 'a1 t

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      type ('elt, 'a) coq_R_fold =
      | R_fold_0 of 'elt t * 'a
      | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
         * ('elt, 'a) coq_R_fold

      val coq_R_fold_rect :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3

      val coq_R_fold_rec :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3

      val fold_rect :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
        t -> 'a2 -> 'a3

      val fold_rec :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
        t -> 'a2 -> 'a3

      val coq_R_fold_correct :
        (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

      type 'elt coq_R_equal =
      | R_equal_0 of 'elt t * 'elt t
      | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
         X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
      | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
         X.t * 'elt * (X.t * 'elt) list * X.t compare0
      | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

      val coq_R_equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
        -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
        X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ ->
        'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
        -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

      val coq_R_equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
        -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
        X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ ->
        'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
        -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

      val equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
        -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
        'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

      val equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
        -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
        'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

      val coq_R_equal_correct :
        ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val option_cons :
        key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
        (key * 'a3) list

      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    val coq_R_mem_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2

    val coq_R_mem_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    val coq_R_find_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

    val coq_R_find_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

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

    val coq_R_bal_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2

    val coq_R_bal_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    val coq_R_add_rect :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

    val coq_R_add_rec :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    val coq_R_remove_min_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree
      -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

    val coq_R_remove_min_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree
      -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    val coq_R_merge_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree
      -> 'a1 coq_R_merge -> 'a2

    val coq_R_merge_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree
      -> 'a1 coq_R_merge -> 'a2

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    val coq_R_remove_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

    val coq_R_remove_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    val coq_R_concat_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat
      -> 'a2

    val coq_R_concat_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat
      -> 'a2

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    val coq_R_split_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2

    val coq_R_split_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    val coq_R_map_option_rect :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3

    val coq_R_map_option_rec :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3

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

    val coq_R_map2_opt_rect :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

    val coq_R_map2_opt_rec :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

    val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    val flatten_e : 'a1 enumeration -> (key * 'a1) list
   end
 end

module Coq0_IntMake :
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val height : 'a1 tree -> I.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> bool

            val lt_dec : X.t -> X.t -> bool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 
           'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * X.t compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
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
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
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
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key * 'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key * 'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree

      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2

      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 
         'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 
         'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
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
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
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
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Coq_Make :
 functor (X:Coq_OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> bool

            val lt_dec : X.t -> X.t -> bool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 
           'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * X.t compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree * (key * 'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key * 'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree

      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 
         'x tree * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

type 'a comparable =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_Comparable *)

val compare1 : 'a1 comparable -> 'a1 -> 'a1 -> comparison

val natComparable : int comparable

val pairComparable :
  'a1 comparable -> 'a2 comparable -> ('a1 * 'a2) comparable

val compare_eqb : 'a1 comparable -> 'a1 -> 'a1 -> bool

type 'a finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

val all_list : 'a1 finite -> 'a1 list

type 'a alphabet = { alphabetComparable : 'a comparable;
                     alphabetFinite : 'a finite }

type 'a numbered = { inj : ('a -> positive); surj : (positive -> 'a);
                     inj_bound : positive }

val numberedAlphabet : 'a1 numbered -> 'a1 alphabet

module type ComparableM =
 sig
  type t

  val tComparable : t comparable
 end

module OrderedTypeAlt_from_ComparableM :
 functor (C:ComparableM) ->
 sig
  type t = C.t

  val compare : t -> t -> comparison
 end

module OrderedType_from_ComparableM :
 functor (C:ComparableM) ->
 sig
  module Alt :
   sig
    type t = C.t

    val compare : t -> t -> comparison
   end

  type t = Alt.t

  val compare : Alt.t -> Alt.t -> Alt.t compare0

  val eq_dec : Alt.t -> Alt.t -> bool
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

module Coq0_Make :
 functor (A:Coq_T) ->
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

module Coq1_Make :
 functor (A:Coq_T) ->
 sig
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
 end

module Coq2_Make :
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
 sig
 end

module Coq3_Make :
 functor (A:Coq_T) ->
 sig
  module TerminalComparableM :
   sig
    type t = A.Gram.terminal

    val tComparable : t comparable
   end

  module TerminalOrderedType :
   sig
    module Alt :
     sig
      type t = TerminalComparableM.t

      val compare : t -> t -> comparison
     end

    type t = Alt.t

    val compare : Alt.t -> Alt.t -> Alt.t compare0

    val eq_dec : Alt.t -> Alt.t -> bool
   end

  module StateProdPosComparableM :
   sig
    type t = (A.state * A.Gram.production) * int

    val tComparable : t comparable
   end

  module StateProdPosOrderedType :
   sig
    module Alt :
     sig
      type t = StateProdPosComparableM.t

      val compare : t -> t -> comparison
     end

    type t = Alt.t

    val compare : Alt.t -> Alt.t -> Alt.t compare0

    val eq_dec : Alt.t -> Alt.t -> bool
   end

  module TerminalSet :
   sig
    module X' :
     sig
      type t = TerminalOrderedType.Alt.t

      val eq_dec :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

      val compare :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> comparison
     end

    module MSet :
     sig
      module Raw :
       sig
        type elt = TerminalOrderedType.Alt.t

        type tree =
        | Leaf
        | Node of Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree

        val empty : tree

        val is_empty : tree -> bool

        val mem : TerminalOrderedType.Alt.t -> tree -> bool

        val min_elt : tree -> elt option

        val max_elt : tree -> elt option

        val choose : tree -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

        val elements_aux :
          TerminalOrderedType.Alt.t list -> tree -> TerminalOrderedType.Alt.t
          list

        val elements : tree -> TerminalOrderedType.Alt.t list

        val rev_elements_aux :
          TerminalOrderedType.Alt.t list -> tree -> TerminalOrderedType.Alt.t
          list

        val rev_elements : tree -> TerminalOrderedType.Alt.t list

        val cardinal : tree -> int

        val maxdepth : tree -> int

        val mindepth : tree -> int

        val for_all : (elt -> bool) -> tree -> bool

        val exists_ : (elt -> bool) -> tree -> bool

        type enumeration =
        | End
        | More of elt * tree * enumeration

        val cons : tree -> enumeration -> enumeration

        val compare_more :
          TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
          enumeration -> comparison

        val compare_cont :
          tree -> (enumeration -> comparison) -> enumeration -> comparison

        val compare_end : enumeration -> comparison

        val compare : tree -> tree -> comparison

        val equal : tree -> tree -> bool

        val subsetl :
          (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

        val subsetr :
          (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

        val subset : tree -> tree -> bool

        type t = tree

        val height : t -> Z_as_Int.t

        val singleton : TerminalOrderedType.Alt.t -> tree

        val create : t -> TerminalOrderedType.Alt.t -> t -> tree

        val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree

        val bal : t -> TerminalOrderedType.Alt.t -> t -> tree

        val add : TerminalOrderedType.Alt.t -> tree -> tree

        val join : tree -> elt -> t -> t

        val remove_min : tree -> elt -> t -> t * elt

        val merge : tree -> tree -> tree

        val remove : TerminalOrderedType.Alt.t -> tree -> tree

        val concat : tree -> tree -> tree

        type triple = { t_left : t; t_in : bool; t_right : t }

        val t_left : triple -> t

        val t_in : triple -> bool

        val t_right : triple -> t

        val split : TerminalOrderedType.Alt.t -> tree -> triple

        val inter : tree -> tree -> tree

        val diff : tree -> tree -> tree

        val union : tree -> tree -> tree

        val filter : (elt -> bool) -> tree -> tree

        val partition : (elt -> bool) -> t -> t * t

        val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool

        val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool

        val isok : tree -> bool

        module MX :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = TerminalOrderedType.Alt.t

              val compare :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                comparison

              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
             end

            module TO :
             sig
              type t = TerminalOrderedType.Alt.t

              val compare :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                comparison

              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
             end
           end

          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

          val lt_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

          val eqb :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end

        type coq_R_min_elt =
        | R_min_elt_0 of tree
        | R_min_elt_1 of tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t
           * tree
        | R_min_elt_2 of tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t
           * tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree
           * elt option * coq_R_min_elt

        type coq_R_max_elt =
        | R_max_elt_0 of tree
        | R_max_elt_1 of tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t
           * tree
        | R_max_elt_2 of tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t
           * tree * Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree
           * elt option * coq_R_max_elt

        module L :
         sig
          module MO :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = TerminalOrderedType.Alt.t

                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison

                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end

              module TO :
               sig
                type t = TerminalOrderedType.Alt.t

                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison

                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end

            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

            val lt_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

            val eqb :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end
         end

        val flatten_e : enumeration -> elt list

        type coq_R_bal =
        | R_bal_0 of t * TerminalOrderedType.Alt.t * t
        | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree
        | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree
        | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_bal_4 of t * TerminalOrderedType.Alt.t * t
        | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree
        | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree
        | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
           tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_bal_8 of t * TerminalOrderedType.Alt.t * t

        type coq_R_remove_min =
        | R_remove_min_0 of tree * elt * t
        | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * (t * elt) * coq_R_remove_min
           * t * elt

        type coq_R_merge =
        | R_merge_0 of tree * tree
        | R_merge_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_merge_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * elt

        type coq_R_concat =
        | R_concat_0 of tree * tree
        | R_concat_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_concat_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * elt

        type coq_R_inter =
        | R_inter_0 of tree * tree
        | R_inter_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_inter_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_inter * tree * coq_R_inter
        | R_inter_3 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_inter * tree * coq_R_inter

        type coq_R_diff =
        | R_diff_0 of tree * tree
        | R_diff_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_diff_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_diff * tree * coq_R_diff
        | R_diff_3 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_diff * tree * coq_R_diff

        type coq_R_union =
        | R_union_0 of tree * tree
        | R_union_1 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree
        | R_union_2 of tree * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
           * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
           * coq_R_union * tree * coq_R_union
       end

      module E :
       sig
        type t = TerminalOrderedType.Alt.t

        val compare :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> comparison

        val eq_dec :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
       end

      type elt = TerminalOrderedType.Alt.t

      type t_ = Raw.t
        (* singleton inductive, whose constructor was Mkt *)

      val this : t_ -> Raw.t

      type t = t_

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val remove : elt -> t -> t

      val singleton : elt -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val empty : t

      val is_empty : t -> bool

      val elements : t -> elt list

      val choose : t -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val cardinal : t -> int

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> t * t

      val eq_dec : t -> t -> bool

      val compare : t -> t -> comparison

      val min_elt : t -> elt option

      val max_elt : t -> elt option
     end

    type elt = TerminalOrderedType.Alt.t

    type t = MSet.t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val eq_dec : t -> t -> bool

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> int

    val elements : t -> elt list

    val choose : t -> elt option

    module MF :
     sig
      val eqb : TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
     end

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val compare : t -> t -> t compare0

    module E :
     sig
      type t = TerminalOrderedType.Alt.t

      val compare :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
        TerminalOrderedType.Alt.t compare0

      val eq_dec :
        TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
     end
   end

  module StateProdPosMap :
   sig
    module E :
     sig
      type t = StateProdPosOrderedType.Alt.t

      val compare :
        StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
        StateProdPosOrderedType.Alt.t compare0

      val eq_dec :
        StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t -> bool
     end

    module Raw :
     sig
      type key = StateProdPosOrderedType.Alt.t

      type 'elt tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val height : 'a1 tree -> Z_as_Int.t

      val cardinal : 'a1 tree -> int

      val empty : 'a1 tree

      val is_empty : 'a1 tree -> bool

      val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool

      val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option

      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

      val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree

      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                           t_right : 'elt tree }

      val t_left : 'a1 triple -> 'a1 tree

      val t_opt : 'a1 triple -> 'a1 option

      val t_right : 'a1 triple -> 'a1 tree

      val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple

      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

      val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

      val elements : 'a1 tree -> (key * 'a1) list

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      type 'elt enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration

      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

      val equal_more :
        ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 -> ('a1
        enumeration -> bool) -> 'a1 enumeration -> bool

      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool

      val equal_end : 'a1 enumeration -> bool

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree

      module Proofs :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = StateProdPosOrderedType.Alt.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            bool

          val lt_dec :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            bool

          val eqb :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = StateProdPosOrderedType.Alt.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool

            val lt_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool

            val eqb :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
           end
         end

        module L :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = StateProdPosOrderedType.Alt.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool

            val lt_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool

            val eqb :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = StateProdPosOrderedType.Alt.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end
           end

          type key = StateProdPosOrderedType.Alt.t

          type 'elt t = (StateProdPosOrderedType.Alt.t * 'elt) list

          val empty : 'a1 t

          val is_empty : 'a1 t -> bool

          val mem : key -> 'a1 t -> bool

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
          | R_mem_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
          | R_mem_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
             * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
            coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
            coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> 'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
          | R_find_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
          | R_find_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt option
             * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
            option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
            option -> 'a1 coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> 'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
          | R_add_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
          | R_add_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt t
             * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> 'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
          | R_remove_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
          | R_remove_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt t
             * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_remove -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_remove -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> 'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * StateProdPosOrderedType.Alt.t * 
             'elt * (StateProdPosOrderedType.Alt.t * 'elt) list * 'a
             * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
            'a2) coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a3 -> 'a3)
            -> 'a1 t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1
            t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a3 -> 'a3)
            -> 'a1 t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          type 'elt coq_R_equal =
          | R_equal_0 of 'elt t * 'elt t
          | R_equal_1 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
             * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
             * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
             * 'elt coq_R_equal
          | R_equal_2 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
             * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
             * StateProdPosOrderedType.Alt.t * 'elt
             * (StateProdPosOrderedType.Alt.t * 'elt) list
             * StateProdPosOrderedType.Alt.t compare0
          | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

          val coq_R_equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

          val coq_R_equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

          val equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t
            -> 'a1 -> (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> 'a2

          val equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
            'a2 -> 'a2) -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t
            -> 'a1 -> (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t -> 'a1 ->
            (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
            StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> 'a2

          val coq_R_equal_correct :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * bool * 'elt coq_R_mem

        val coq_R_mem_rect :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

        type 'elt coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt option * 'elt coq_R_find

        val coq_R_find_rect :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

        type 'elt coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2

        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
          -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
          __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          -> 'a1 coq_R_bal -> 'a2

        type 'elt coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree
          -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 coq_R_add -> 'a2

        type 'elt coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree * (key * 'elt))
           * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        type 'elt coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 ->
          __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
          -> 'a2

        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 ->
          __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
          -> 'a2

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

        val coq_R_remove_rect :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

        type 'elt coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt tree * (key * 'elt)

        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        type 'elt coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree

        val coq_R_split_rect :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
          coq_R_split -> 'a2

        val coq_R_split_rec :
          StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
          __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
          coq_R_split -> 'a2

        type ('elt, 'x) coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
           * 'x tree * ('elt, 'x) coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
           * ('elt, 'x) coq_R_map_option

        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3

        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 ->
          __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3

        type ('elt, 'x0, 'x) coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'x0 tree
        | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t
        | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt

        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4

        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key ->
          'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option ->
          'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
          tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
          __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
          'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
          tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
          'a4

        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        val flatten_e : 'a1 enumeration -> (key * 'a1) list
       end
     end

    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)

    val this : 'a1 bst -> 'a1 Raw.tree

    type 'elt t = 'elt bst

    type key = StateProdPosOrderedType.Alt.t

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    val remove : key -> 'a1 t -> 'a1 t

    val mem : key -> 'a1 t -> bool

    val find : key -> 'a1 t -> 'a1 option

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

    val elements : 'a1 t -> (key * 'a1) list

    val cardinal : 'a1 t -> int

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end

  val nullable_symb : A.Gram.symbol -> bool

  val nullable_word : A.Gram.symbol list -> bool

  val first_nterm_set : A.Gram.nonterminal -> TerminalSet.t

  val first_symb_set : A.Gram.symbol -> TerminalSet.t

  val first_word_set : A.Gram.symbol list -> TerminalSet.t

  val future_of_prod : A.Gram.production -> int -> A.Gram.symbol list

  val items_map : unit -> TerminalSet.t StateProdPosMap.t

  val find_items_map :
    TerminalSet.t StateProdPosMap.t -> A.state -> A.Gram.production -> int ->
    TerminalSet.t

  val forallb_items :
    TerminalSet.t StateProdPosMap.t -> (A.state -> A.Gram.production -> int
    -> TerminalSet.t -> bool) -> bool

  val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool

  val is_complete_0 : TerminalSet.t StateProdPosMap.t -> bool

  val is_complete : unit -> bool
 end

module Coq4_Make :
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
 sig
  module Valid :
   sig
    module TerminalComparableM :
     sig
      type t = A.Gram.terminal

      val tComparable : t comparable
     end

    module TerminalOrderedType :
     sig
      module Alt :
       sig
        type t = TerminalComparableM.t

        val compare : t -> t -> comparison
       end

      type t = Alt.t

      val compare : Alt.t -> Alt.t -> Alt.t compare0

      val eq_dec : Alt.t -> Alt.t -> bool
     end

    module StateProdPosComparableM :
     sig
      type t = (A.state * A.Gram.production) * int

      val tComparable : t comparable
     end

    module StateProdPosOrderedType :
     sig
      module Alt :
       sig
        type t = StateProdPosComparableM.t

        val compare : t -> t -> comparison
       end

      type t = Alt.t

      val compare : Alt.t -> Alt.t -> Alt.t compare0

      val eq_dec : Alt.t -> Alt.t -> bool
     end

    module TerminalSet :
     sig
      module X' :
       sig
        type t = TerminalOrderedType.Alt.t

        val eq_dec :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

        val compare :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> comparison
       end

      module MSet :
       sig
        module Raw :
         sig
          type elt = TerminalOrderedType.Alt.t

          type tree =
          | Leaf
          | Node of Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree

          val empty : tree

          val is_empty : tree -> bool

          val mem : TerminalOrderedType.Alt.t -> tree -> bool

          val min_elt : tree -> elt option

          val max_elt : tree -> elt option

          val choose : tree -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

          val elements_aux :
            TerminalOrderedType.Alt.t list -> tree ->
            TerminalOrderedType.Alt.t list

          val elements : tree -> TerminalOrderedType.Alt.t list

          val rev_elements_aux :
            TerminalOrderedType.Alt.t list -> tree ->
            TerminalOrderedType.Alt.t list

          val rev_elements : tree -> TerminalOrderedType.Alt.t list

          val cardinal : tree -> int

          val maxdepth : tree -> int

          val mindepth : tree -> int

          val for_all : (elt -> bool) -> tree -> bool

          val exists_ : (elt -> bool) -> tree -> bool

          type enumeration =
          | End
          | More of elt * tree * enumeration

          val cons : tree -> enumeration -> enumeration

          val compare_more :
            TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
            enumeration -> comparison

          val compare_cont :
            tree -> (enumeration -> comparison) -> enumeration -> comparison

          val compare_end : enumeration -> comparison

          val compare : tree -> tree -> comparison

          val equal : tree -> tree -> bool

          val subsetl :
            (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

          val subsetr :
            (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

          val subset : tree -> tree -> bool

          type t = tree

          val height : t -> Z_as_Int.t

          val singleton : TerminalOrderedType.Alt.t -> tree

          val create : t -> TerminalOrderedType.Alt.t -> t -> tree

          val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree

          val bal : t -> TerminalOrderedType.Alt.t -> t -> tree

          val add : TerminalOrderedType.Alt.t -> tree -> tree

          val join : tree -> elt -> t -> t

          val remove_min : tree -> elt -> t -> t * elt

          val merge : tree -> tree -> tree

          val remove : TerminalOrderedType.Alt.t -> tree -> tree

          val concat : tree -> tree -> tree

          type triple = { t_left : t; t_in : bool; t_right : t }

          val t_left : triple -> t

          val t_in : triple -> bool

          val t_right : triple -> t

          val split : TerminalOrderedType.Alt.t -> tree -> triple

          val inter : tree -> tree -> tree

          val diff : tree -> tree -> tree

          val union : tree -> tree -> tree

          val filter : (elt -> bool) -> tree -> tree

          val partition : (elt -> bool) -> t -> t * t

          val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool

          val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool

          val isok : tree -> bool

          module MX :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = TerminalOrderedType.Alt.t

                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison

                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end

              module TO :
               sig
                type t = TerminalOrderedType.Alt.t

                val compare :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  comparison

                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end

            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

            val lt_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

            val eqb :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end

          type coq_R_min_elt =
          | R_min_elt_0 of tree
          | R_min_elt_1 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_min_elt_2 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * elt option * coq_R_min_elt

          type coq_R_max_elt =
          | R_max_elt_0 of tree
          | R_max_elt_1 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_max_elt_2 of tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * elt option * coq_R_max_elt

          module L :
           sig
            module MO :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = TerminalOrderedType.Alt.t

                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison

                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end

                module TO :
                 sig
                  type t = TerminalOrderedType.Alt.t

                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison

                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
               end

              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
             end
           end

          val flatten_e : enumeration -> elt list

          type coq_R_bal =
          | R_bal_0 of t * TerminalOrderedType.Alt.t * t
          | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_bal_4 of t * TerminalOrderedType.Alt.t * t
          | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree
          | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t * 
             tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_bal_8 of t * TerminalOrderedType.Alt.t * t

          type coq_R_remove_min =
          | R_remove_min_0 of tree * elt * t
          | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * (t * elt)
             * coq_R_remove_min * t * elt

          type coq_R_merge =
          | R_merge_0 of tree * tree
          | R_merge_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_merge_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * elt

          type coq_R_concat =
          | R_concat_0 of tree * tree
          | R_concat_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_concat_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * elt

          type coq_R_inter =
          | R_inter_0 of tree * tree
          | R_inter_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_inter_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_inter * tree * coq_R_inter
          | R_inter_3 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_inter * tree * coq_R_inter

          type coq_R_diff =
          | R_diff_0 of tree * tree
          | R_diff_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_diff_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_diff * tree * coq_R_diff
          | R_diff_3 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_diff * tree * coq_R_diff

          type coq_R_union =
          | R_union_0 of tree * tree
          | R_union_1 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree
          | R_union_2 of tree * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
             * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
             * coq_R_union * tree * coq_R_union
         end

        module E :
         sig
          type t = TerminalOrderedType.Alt.t

          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison

          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end

        type elt = TerminalOrderedType.Alt.t

        type t_ = Raw.t
          (* singleton inductive, whose constructor was Mkt *)

        val this : t_ -> Raw.t

        type t = t_

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val remove : elt -> t -> t

        val singleton : elt -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val empty : t

        val is_empty : t -> bool

        val elements : t -> elt list

        val choose : t -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val cardinal : t -> int

        val filter : (elt -> bool) -> t -> t

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val partition : (elt -> bool) -> t -> t * t

        val eq_dec : t -> t -> bool

        val compare : t -> t -> comparison

        val min_elt : t -> elt option

        val max_elt : t -> elt option
       end

      type elt = TerminalOrderedType.Alt.t

      type t = MSet.t

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val eq_dec : t -> t -> bool

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> int

      val elements : t -> elt list

      val choose : t -> elt option

      module MF :
       sig
        val eqb :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
       end

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val compare : t -> t -> t compare0

      module E :
       sig
        type t = TerminalOrderedType.Alt.t

        val compare :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
          TerminalOrderedType.Alt.t compare0

        val eq_dec :
          TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
       end
     end

    module StateProdPosMap :
     sig
      module E :
       sig
        type t = StateProdPosOrderedType.Alt.t

        val compare :
          StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
          StateProdPosOrderedType.Alt.t compare0

        val eq_dec :
          StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
          bool
       end

      module Raw :
       sig
        type key = StateProdPosOrderedType.Alt.t

        type 'elt tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val height : 'a1 tree -> Z_as_Int.t

        val cardinal : 'a1 tree -> int

        val empty : 'a1 tree

        val is_empty : 'a1 tree -> bool

        val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool

        val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option

        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

        val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree

        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                             t_right : 'elt tree }

        val t_left : 'a1 triple -> 'a1 tree

        val t_opt : 'a1 triple -> 'a1 option

        val t_right : 'a1 triple -> 'a1 tree

        val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple

        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

        val elements : 'a1 tree -> (key * 'a1) list

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        type 'elt enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration

        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

        val equal_more :
          ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 ->
          ('a1 enumeration -> bool) -> 'a1 enumeration -> bool

        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_end : 'a1 enumeration -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree

        module Proofs :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = StateProdPosOrderedType.Alt.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool

            val lt_dec :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool

            val eqb :
              StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t
              -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = StateProdPosOrderedType.Alt.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end
           end

          module L :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = StateProdPosOrderedType.Alt.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = StateProdPosOrderedType.Alt.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end
             end

            type key = StateProdPosOrderedType.Alt.t

            type 'elt t = (StateProdPosOrderedType.Alt.t * 'elt) list

            val empty : 'a1 t

            val is_empty : 'a1 t -> bool

            val mem : key -> 'a1 t -> bool

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_mem_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_mem_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
               * 'elt coq_R_mem

            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
              coq_R_mem -> 'a2

            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
              coq_R_mem -> 'a2

            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2

            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

            val find : key -> 'a1 t -> 'a1 option

            type 'elt coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_find_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_find_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt option
               * 'elt coq_R_find

            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
              option -> 'a1 coq_R_find -> 'a2

            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
              option -> 'a1 coq_R_find -> 'a2

            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2

            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

            val add : key -> 'a1 -> 'a1 t -> 'a1 t

            type 'elt coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_add_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_add_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt t
               * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_add -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_add -> 'a2

            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2

            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

            val remove : key -> 'a1 t -> 'a1 t

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_remove_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
            | R_remove_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt t
               * 'elt coq_R_remove

            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
              'a1 coq_R_remove -> 'a2

            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
              'a1 coq_R_remove -> 'a2

            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2

            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

            val elements : 'a1 t -> 'a1 t

            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

            type ('elt, 'a) coq_R_fold =
            | R_fold_0 of 'elt t * 'a
            | R_fold_1 of 'elt t * 'a * StateProdPosOrderedType.Alt.t * 
               'elt * (StateProdPosOrderedType.Alt.t * 'elt) list * 'a
               * ('elt, 'a) coq_R_fold

            val coq_R_fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 ->
              ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 ->
              ('a1, 'a2) coq_R_fold -> 'a3

            val coq_R_fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 ->
              ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 ->
              ('a1, 'a2) coq_R_fold -> 'a3

            val fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a3 -> 'a3)
              -> 'a1 t -> 'a2 -> 'a3

            val fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a3 -> 'a3)
              -> 'a1 t -> 'a2 -> 'a3

            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold

            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

            type 'elt coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
               * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
               * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
               * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
               * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
               * StateProdPosOrderedType.Alt.t * 'elt
               * (StateProdPosOrderedType.Alt.t * 'elt) list
               * StateProdPosOrderedType.Alt.t compare0
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
              'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
              'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t
              -> 'a1 -> (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
              'a1 t -> 'a1 t -> 'a2

            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __ ->
              'a2 -> 'a2) -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t
              -> 'a1 -> (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t -> 'a1 ->
              (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
              StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
              'a1 t -> 'a1 t -> 'a2

            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal

            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t

            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list

            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
            'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
            'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

          type 'elt coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
            coq_R_find -> 'a2

          val coq_R_find_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
            coq_R_find -> 'a2

          type 'elt coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          type 'elt coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          type 'elt coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)

          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          type 'elt coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

          val coq_R_remove_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2

          val coq_R_remove_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_remove -> 'a2

          type 'elt coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt)

          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          type 'elt coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree

          val coq_R_split_rect :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
            'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1
            tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
            triple -> 'a1 coq_R_split -> 'a2

          val coq_R_split_rec :
            StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
            'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1
            tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
            triple -> 'a1 coq_R_split -> 'a2

          type ('elt, 'x) coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
             * ('elt, 'x) coq_R_map_option

          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          type ('elt, 'x0, 'x) coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'x0 tree
          | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt

          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end

      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)

      val this : 'a1 bst -> 'a1 Raw.tree

      type 'elt t = 'elt bst

      type key = StateProdPosOrderedType.Alt.t

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val elements : 'a1 t -> (key * 'a1) list

      val cardinal : 'a1 t -> int

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end

    val nullable_symb : A.Gram.symbol -> bool

    val nullable_word : A.Gram.symbol list -> bool

    val first_nterm_set : A.Gram.nonterminal -> TerminalSet.t

    val first_symb_set : A.Gram.symbol -> TerminalSet.t

    val first_word_set : A.Gram.symbol list -> TerminalSet.t

    val future_of_prod : A.Gram.production -> int -> A.Gram.symbol list

    val items_map : unit -> TerminalSet.t StateProdPosMap.t

    val find_items_map :
      TerminalSet.t StateProdPosMap.t -> A.state -> A.Gram.production -> int
      -> TerminalSet.t

    val forallb_items :
      TerminalSet.t StateProdPosMap.t -> (A.state -> A.Gram.production -> int
      -> TerminalSet.t -> bool) -> bool

    val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool

    val is_complete_0 : TerminalSet.t StateProdPosMap.t -> bool

    val is_complete : unit -> bool
   end

  type pt_zipper =
  | Top_ptz
  | Cons_ptl_ptz of A.Gram.symbol list * A.Gram.token list
     * A.GramDefs.parse_tree_list * A.Gram.symbol * A.Gram.token list
     * ptl_zipper
  and ptl_zipper =
  | Non_terminal_pt_ptlz of A.Gram.production * A.Gram.token list * pt_zipper
  | Cons_ptl_ptlz of A.Gram.symbol list * A.Gram.token list * A.Gram.symbol
     * A.Gram.token list * A.GramDefs.parse_tree * ptl_zipper

  val pt_zipper_rect :
    A.initstate -> A.Gram.token list -> 'a1 -> (A.Gram.symbol list ->
    A.Gram.token list -> A.GramDefs.parse_tree_list -> A.Gram.symbol ->
    A.Gram.token list -> ptl_zipper -> 'a1) -> A.Gram.symbol -> A.Gram.token
    list -> pt_zipper -> 'a1

  val pt_zipper_rec :
    A.initstate -> A.Gram.token list -> 'a1 -> (A.Gram.symbol list ->
    A.Gram.token list -> A.GramDefs.parse_tree_list -> A.Gram.symbol ->
    A.Gram.token list -> ptl_zipper -> 'a1) -> A.Gram.symbol -> A.Gram.token
    list -> pt_zipper -> 'a1

  val ptl_zipper_rect :
    A.initstate -> A.Gram.token list -> (A.Gram.production -> A.Gram.token
    list -> pt_zipper -> 'a1) -> (A.Gram.symbol list -> A.Gram.token list ->
    A.Gram.symbol -> A.Gram.token list -> A.GramDefs.parse_tree -> ptl_zipper
    -> 'a1 -> 'a1) -> A.Gram.symbol list -> A.Gram.token list -> ptl_zipper
    -> 'a1

  val ptl_zipper_rec :
    A.initstate -> A.Gram.token list -> (A.Gram.production -> A.Gram.token
    list -> pt_zipper -> 'a1) -> (A.Gram.symbol list -> A.Gram.token list ->
    A.Gram.symbol -> A.Gram.token list -> A.GramDefs.parse_tree -> ptl_zipper
    -> 'a1 -> 'a1) -> A.Gram.symbol list -> A.Gram.token list -> ptl_zipper
    -> 'a1

  type pt_dot =
  | Reduce_ptd of A.Gram.production * A.Gram.token list
     * A.GramDefs.parse_tree_list * pt_zipper
  | Shift_ptd of A.Gram.token * A.Gram.symbol list * A.Gram.token list
     * A.GramDefs.parse_tree_list * ptl_zipper

  val pt_dot_rect :
    A.initstate -> A.Gram.token list -> (A.Gram.production -> A.Gram.token
    list -> A.GramDefs.parse_tree_list -> pt_zipper -> 'a1) -> (A.Gram.token
    -> A.Gram.symbol list -> A.Gram.token list -> A.GramDefs.parse_tree_list
    -> ptl_zipper -> 'a1) -> pt_dot -> 'a1

  val pt_dot_rec :
    A.initstate -> A.Gram.token list -> (A.Gram.production -> A.Gram.token
    list -> A.GramDefs.parse_tree_list -> pt_zipper -> 'a1) -> (A.Gram.token
    -> A.Gram.symbol list -> A.Gram.token list -> A.GramDefs.parse_tree_list
    -> ptl_zipper -> 'a1) -> pt_dot -> 'a1

  val ptlz_sem :
    A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
    list -> ptl_zipper -> (__ -> __ arrows_right -> __) ->
    A.Gram.symbol_semantic_type

  val ptz_sem :
    A.initstate -> A.Gram.token list -> A.Gram.symbol -> A.Gram.token list ->
    pt_zipper -> A.Gram.symbol_semantic_type -> A.Gram.symbol_semantic_type

  val ptd_sem :
    A.initstate -> A.Gram.token list -> pt_dot -> A.Gram.symbol_semantic_type

  val ptlz_buffer :
    A.initstate -> A.Gram.token list -> Inter.buffer -> A.Gram.symbol list ->
    A.Gram.token list -> ptl_zipper -> Inter.buffer

  val ptz_buffer :
    A.initstate -> A.Gram.token list -> Inter.buffer -> A.Gram.symbol ->
    A.Gram.token list -> pt_zipper -> Inter.buffer

  val ptd_buffer :
    A.initstate -> A.Gram.token list -> Inter.buffer -> pt_dot -> Inter.buffer

  val ptlz_prod :
    A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
    list -> ptl_zipper -> A.Gram.production

  val ptlz_future :
    A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
    list -> ptl_zipper -> A.Gram.symbol list

  val ptlz_lookahead :
    A.initstate -> A.Gram.token list -> Inter.buffer -> A.Gram.symbol list ->
    A.Gram.token list -> ptl_zipper -> A.Gram.terminal

  val build_pt_dot_from_pt :
    A.initstate -> A.Gram.token list -> A.Gram.symbol -> A.Gram.token list ->
    A.GramDefs.parse_tree -> pt_zipper -> pt_dot

  val build_pt_dot_from_pt_rec :
    A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
    list -> A.GramDefs.parse_tree_list -> ptl_zipper -> pt_dot

  val build_pt_dot_from_ptl :
    A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
    list -> A.GramDefs.parse_tree_list -> ptl_zipper -> pt_dot

  val next_ptd : A.initstate -> A.Gram.token list -> pt_dot -> pt_dot option

  val next_ptd_iter :
    A.initstate -> A.Gram.token list -> pt_dot -> int -> pt_dot option

  val ptlz_cost :
    A.initstate -> A.Gram.token list -> A.Gram.symbol list -> A.Gram.token
    list -> ptl_zipper -> int

  val ptz_cost :
    A.initstate -> A.Gram.token list -> A.Gram.symbol -> A.Gram.token list ->
    pt_zipper -> int

  val ptd_cost : A.initstate -> A.Gram.token list -> pt_dot -> int
 end

module Coq5_Make :
 functor (Aut:Coq_T) ->
 sig
  module Inter :
   sig
    module ValidSafe :
     sig
      val singleton_state_pred : Aut.state -> Aut.state -> bool

      val past_state_of_state : Aut.state -> (Aut.state -> bool) list

      val head_symbs_of_state : Aut.state -> Aut.Gram.symbol list

      val head_states_of_state : Aut.state -> (Aut.state -> bool) list

      val is_prefix : Aut.Gram.symbol list -> Aut.Gram.symbol list -> bool

      val is_prefix_pred :
        (Aut.state -> bool) list -> (Aut.state -> bool) list -> bool

      val is_state_valid_after_pop :
        Aut.state -> Aut.Gram.symbol list -> (Aut.state -> bool) list -> bool

      val is_safe : unit -> bool
     end

    type coq_Decidable = bool

    val decide : coq_Decidable -> bool

    val comparable_decidable_eq :
      'a1 comparable -> 'a1 -> 'a1 -> coq_Decidable

    val list_decidable_eq :
      ('a1 -> 'a1 -> coq_Decidable) -> 'a1 list -> 'a1 list -> coq_Decidable

    val cast : 'a1 -> 'a1 -> (unit -> coq_Decidable) -> 'a2 -> 'a2

    type buffer = __buffer Lazy.t
    and __buffer =
    | Buf_cons of Aut.Gram.token * buffer

    val buf_head : buffer -> Aut.Gram.token

    val buf_tail : buffer -> buffer

    val app_buf : Aut.Gram.token list -> buffer -> buffer

    type noninitstate_type = Aut.Gram.symbol_semantic_type

    type stack = (Aut.noninitstate, noninitstate_type) sigT list

    val state_of_stack : Aut.initstate -> stack -> Aut.state

    val state_stack_of_stack :
      Aut.initstate -> stack -> (Aut.state -> bool) list

    val symb_stack_of_stack : stack -> Aut.Gram.symbol list

    val pop : Aut.Gram.symbol list -> stack -> 'a1 arrows_right -> stack * 'a1

    type step_result =
    | Fail_sr_full of Aut.state * Aut.Gram.token
    | Accept_sr of Aut.Gram.symbol_semantic_type * buffer
    | Progress_sr of stack * buffer

    val step_result_rect :
      Aut.initstate -> (Aut.state -> Aut.Gram.token -> 'a1) ->
      (Aut.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
      'a1) -> step_result -> 'a1

    val step_result_rec :
      Aut.initstate -> (Aut.state -> Aut.Gram.token -> 'a1) ->
      (Aut.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
      'a1) -> step_result -> 'a1

    val reduce_step :
      Aut.initstate -> stack -> Aut.Gram.production -> buffer -> step_result

    val step : Aut.initstate -> stack -> buffer -> step_result

    val parse_fix : Aut.initstate -> stack -> buffer -> int -> step_result

    type 'a parse_result =
    | Fail_pr_full of Aut.state * Aut.Gram.token
    | Timeout_pr
    | Parsed_pr of 'a * buffer

    val parse_result_rect :
      (Aut.state -> Aut.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2)
      -> 'a1 parse_result -> 'a2

    val parse_result_rec :
      (Aut.state -> Aut.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2)
      -> 'a1 parse_result -> 'a2

    val parse :
      Aut.initstate -> buffer -> int -> Aut.Gram.symbol_semantic_type
      parse_result
   end

  module Correct :
   sig
   end

  module Complete :
   sig
    module Valid :
     sig
      module TerminalComparableM :
       sig
        type t = Aut.Gram.terminal

        val tComparable : t comparable
       end

      module TerminalOrderedType :
       sig
        module Alt :
         sig
          type t = TerminalComparableM.t

          val compare : t -> t -> comparison
         end

        type t = Alt.t

        val compare : Alt.t -> Alt.t -> Alt.t compare0

        val eq_dec : Alt.t -> Alt.t -> bool
       end

      module StateProdPosComparableM :
       sig
        type t = (Aut.state * Aut.Gram.production) * int

        val tComparable : t comparable
       end

      module StateProdPosOrderedType :
       sig
        module Alt :
         sig
          type t = StateProdPosComparableM.t

          val compare : t -> t -> comparison
         end

        type t = Alt.t

        val compare : Alt.t -> Alt.t -> Alt.t compare0

        val eq_dec : Alt.t -> Alt.t -> bool
       end

      module TerminalSet :
       sig
        module X' :
         sig
          type t = TerminalOrderedType.Alt.t

          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison
         end

        module MSet :
         sig
          module Raw :
           sig
            type elt = TerminalOrderedType.Alt.t

            type tree =
            | Leaf
            | Node of Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree

            val empty : tree

            val is_empty : tree -> bool

            val mem : TerminalOrderedType.Alt.t -> tree -> bool

            val min_elt : tree -> elt option

            val max_elt : tree -> elt option

            val choose : tree -> elt option

            val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

            val elements_aux :
              TerminalOrderedType.Alt.t list -> tree ->
              TerminalOrderedType.Alt.t list

            val elements : tree -> TerminalOrderedType.Alt.t list

            val rev_elements_aux :
              TerminalOrderedType.Alt.t list -> tree ->
              TerminalOrderedType.Alt.t list

            val rev_elements : tree -> TerminalOrderedType.Alt.t list

            val cardinal : tree -> int

            val maxdepth : tree -> int

            val mindepth : tree -> int

            val for_all : (elt -> bool) -> tree -> bool

            val exists_ : (elt -> bool) -> tree -> bool

            type enumeration =
            | End
            | More of elt * tree * enumeration

            val cons : tree -> enumeration -> enumeration

            val compare_more :
              TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
              enumeration -> comparison

            val compare_cont :
              tree -> (enumeration -> comparison) -> enumeration -> comparison

            val compare_end : enumeration -> comparison

            val compare : tree -> tree -> comparison

            val equal : tree -> tree -> bool

            val subsetl :
              (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

            val subsetr :
              (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

            val subset : tree -> tree -> bool

            type t = tree

            val height : t -> Z_as_Int.t

            val singleton : TerminalOrderedType.Alt.t -> tree

            val create : t -> TerminalOrderedType.Alt.t -> t -> tree

            val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree

            val bal : t -> TerminalOrderedType.Alt.t -> t -> tree

            val add : TerminalOrderedType.Alt.t -> tree -> tree

            val join : tree -> elt -> t -> t

            val remove_min : tree -> elt -> t -> t * elt

            val merge : tree -> tree -> tree

            val remove : TerminalOrderedType.Alt.t -> tree -> tree

            val concat : tree -> tree -> tree

            type triple = { t_left : t; t_in : bool; t_right : t }

            val t_left : triple -> t

            val t_in : triple -> bool

            val t_right : triple -> t

            val split : TerminalOrderedType.Alt.t -> tree -> triple

            val inter : tree -> tree -> tree

            val diff : tree -> tree -> tree

            val union : tree -> tree -> tree

            val filter : (elt -> bool) -> tree -> tree

            val partition : (elt -> bool) -> t -> t * t

            val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool

            val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool

            val isok : tree -> bool

            module MX :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = TerminalOrderedType.Alt.t

                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison

                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end

                module TO :
                 sig
                  type t = TerminalOrderedType.Alt.t

                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison

                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
               end

              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
             end

            type coq_R_min_elt =
            | R_min_elt_0 of tree
            | R_min_elt_1 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_min_elt_2 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * elt option * coq_R_min_elt

            type coq_R_max_elt =
            | R_max_elt_0 of tree
            | R_max_elt_1 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_max_elt_2 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * elt option * coq_R_max_elt

            module L :
             sig
              module MO :
               sig
                module OrderTac :
                 sig
                  module OTF :
                   sig
                    type t = TerminalOrderedType.Alt.t

                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison

                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end

                  module TO :
                   sig
                    type t = TerminalOrderedType.Alt.t

                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison

                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end
                 end

                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool

                val lt_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool

                val eqb :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end

            val flatten_e : enumeration -> elt list

            type coq_R_bal =
            | R_bal_0 of t * TerminalOrderedType.Alt.t * t
            | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree
            | R_bal_4 of t * TerminalOrderedType.Alt.t * t
            | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree
            | R_bal_8 of t * TerminalOrderedType.Alt.t * t

            type coq_R_remove_min =
            | R_remove_min_0 of tree * elt * t
            | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * (t * elt)
               * coq_R_remove_min * t * elt

            type coq_R_merge =
            | R_merge_0 of tree * tree
            | R_merge_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_merge_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * elt

            type coq_R_concat =
            | R_concat_0 of tree * tree
            | R_concat_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_concat_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * elt

            type coq_R_inter =
            | R_inter_0 of tree * tree
            | R_inter_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_inter_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_inter * tree * coq_R_inter
            | R_inter_3 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_inter * tree * coq_R_inter

            type coq_R_diff =
            | R_diff_0 of tree * tree
            | R_diff_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_diff_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_diff * tree * coq_R_diff
            | R_diff_3 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_diff * tree * coq_R_diff

            type coq_R_union =
            | R_union_0 of tree * tree
            | R_union_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_union_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_union * tree * coq_R_union
           end

          module E :
           sig
            type t = TerminalOrderedType.Alt.t

            val compare :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              comparison

            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end

          type elt = TerminalOrderedType.Alt.t

          type t_ = Raw.t
            (* singleton inductive, whose constructor was Mkt *)

          val this : t_ -> Raw.t

          type t = t_

          val mem : elt -> t -> bool

          val add : elt -> t -> t

          val remove : elt -> t -> t

          val singleton : elt -> t

          val union : t -> t -> t

          val inter : t -> t -> t

          val diff : t -> t -> t

          val equal : t -> t -> bool

          val subset : t -> t -> bool

          val empty : t

          val is_empty : t -> bool

          val elements : t -> elt list

          val choose : t -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

          val cardinal : t -> int

          val filter : (elt -> bool) -> t -> t

          val for_all : (elt -> bool) -> t -> bool

          val exists_ : (elt -> bool) -> t -> bool

          val partition : (elt -> bool) -> t -> t * t

          val eq_dec : t -> t -> bool

          val compare : t -> t -> comparison

          val min_elt : t -> elt option

          val max_elt : t -> elt option
         end

        type elt = TerminalOrderedType.Alt.t

        type t = MSet.t

        val empty : t

        val is_empty : t -> bool

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val singleton : elt -> t

        val remove : elt -> t -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val eq_dec : t -> t -> bool

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val filter : (elt -> bool) -> t -> t

        val partition : (elt -> bool) -> t -> t * t

        val cardinal : t -> int

        val elements : t -> elt list

        val choose : t -> elt option

        module MF :
         sig
          val eqb :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end

        val min_elt : t -> elt option

        val max_elt : t -> elt option

        val compare : t -> t -> t compare0

        module E :
         sig
          type t = TerminalOrderedType.Alt.t

          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            TerminalOrderedType.Alt.t compare0

          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
       end

      module StateProdPosMap :
       sig
        module E :
         sig
          type t = StateProdPosOrderedType.Alt.t

          val compare :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            StateProdPosOrderedType.Alt.t compare0

          val eq_dec :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            bool
         end

        module Raw :
         sig
          type key = StateProdPosOrderedType.Alt.t

          type 'elt tree =
          | Leaf
          | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

          val tree_rect :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val tree_rec :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val height : 'a1 tree -> Z_as_Int.t

          val cardinal : 'a1 tree -> int

          val empty : 'a1 tree

          val is_empty : 'a1 tree -> bool

          val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool

          val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option

          val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

          val remove_min :
            'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

          val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

          val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree

          val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                               t_right : 'elt tree }

          val t_left : 'a1 triple -> 'a1 tree

          val t_opt : 'a1 triple -> 'a1 option

          val t_right : 'a1 triple -> 'a1 tree

          val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple

          val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

          val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

          val elements : 'a1 tree -> (key * 'a1) list

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          type 'elt enumeration =
          | End
          | More of key * 'elt * 'elt tree * 'elt enumeration

          val enumeration_rect :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val enumeration_rec :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

          val equal_more :
            ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            ('a1 enumeration -> bool) -> 'a1 enumeration -> bool

          val equal_cont :
            ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
            'a1 enumeration -> bool

          val equal_end : 'a1 enumeration -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

          val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

          val map2_opt :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3
            tree

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree
            -> 'a3 tree

          module Proofs :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = StateProdPosOrderedType.Alt.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = StateProdPosOrderedType.Alt.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end
             end

            module L :
             sig
              module MX :
               sig
                module TO :
                 sig
                  type t = StateProdPosOrderedType.Alt.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end

              module PX :
               sig
                module MO :
                 sig
                  module TO :
                   sig
                    type t = StateProdPosOrderedType.Alt.t
                   end

                  module IsTO :
                   sig
                   end

                  module OrderTac :
                   sig
                   end

                  val eq_dec :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool

                  val lt_dec :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool

                  val eqb :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool
                 end
               end

              type key = StateProdPosOrderedType.Alt.t

              type 'elt t = (StateProdPosOrderedType.Alt.t * 'elt) list

              val empty : 'a1 t

              val is_empty : 'a1 t -> bool

              val mem : key -> 'a1 t -> bool

              type 'elt coq_R_mem =
              | R_mem_0 of 'elt t
              | R_mem_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_mem_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_mem_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
                 * 'elt coq_R_mem

              val coq_R_mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
                'a1 coq_R_mem -> 'a2

              val coq_R_mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
                'a1 coq_R_mem -> 'a2

              val mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

              val find : key -> 'a1 t -> 'a1 option

              type 'elt coq_R_find =
              | R_find_0 of 'elt t
              | R_find_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_find_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_find_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
                 * 'elt option * 'elt coq_R_find

              val coq_R_find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 option -> 'a1 coq_R_find -> 'a2

              val coq_R_find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 option -> 'a1 coq_R_find -> 'a2

              val find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val coq_R_find_correct :
                key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

              val add : key -> 'a1 -> 'a1 t -> 'a1 t

              type 'elt coq_R_add =
              | R_add_0 of 'elt t
              | R_add_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_add_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_add_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt t
                 * 'elt coq_R_add

              val coq_R_add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
                'a1 coq_R_add -> 'a2

              val coq_R_add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
                'a1 coq_R_add -> 'a2

              val add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val coq_R_add_correct :
                key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

              val remove : key -> 'a1 t -> 'a1 t

              type 'elt coq_R_remove =
              | R_remove_0 of 'elt t
              | R_remove_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_remove_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_remove_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list * 
                 'elt t * 'elt coq_R_remove

              val coq_R_remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
                -> 'a1 coq_R_remove -> 'a2

              val coq_R_remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
                -> 'a1 coq_R_remove -> 'a2

              val remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val coq_R_remove_correct :
                key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

              val elements : 'a1 t -> 'a1 t

              val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

              type ('elt, 'a) coq_R_fold =
              | R_fold_0 of 'elt t * 'a
              | R_fold_1 of 'elt t * 'a * StateProdPosOrderedType.Alt.t
                 * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list * 
                 'a * ('elt, 'a) coq_R_fold

              val coq_R_fold_rect :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 ->
                ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
                -> ('a1, 'a2) coq_R_fold -> 'a3

              val coq_R_fold_rec :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 ->
                ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
                -> ('a1, 'a2) coq_R_fold -> 'a3

              val fold_rect :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a3 ->
                'a3) -> 'a1 t -> 'a2 -> 'a3

              val fold_rec :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a3 ->
                'a3) -> 'a1 t -> 'a2 -> 'a3

              val coq_R_fold_correct :
                (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold

              val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

              type 'elt coq_R_equal =
              | R_equal_0 of 'elt t * 'elt t
              | R_equal_1 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
                 * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
                 * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
                 * 'elt coq_R_equal
              | R_equal_2 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
                 * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
                 * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
                 * StateProdPosOrderedType.Alt.t compare0
              | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

              val coq_R_equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
                -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

              val coq_R_equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
                -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

              val equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> 'a2

              val equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> 'a2

              val coq_R_equal_correct :
                ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal

              val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

              val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

              val option_cons :
                key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

              val map2_l :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

              val map2_r :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

              val map2 :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                'a3 t

              val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

              val fold_right_pair :
                ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

              val map2_alt :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                (key * 'a3) list

              val at_least_one :
                'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

              val at_least_one_then_f :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
                option -> 'a3 option
             end

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt tree
            | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem
            | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem
              -> 'a2

            val coq_R_mem_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem
              -> 'a2

            type 'elt coq_R_find =
            | R_find_0 of 'elt tree
            | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find
            | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              option -> 'a1 coq_R_find -> 'a2

            val coq_R_find_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              option -> 'a1 coq_R_find -> 'a2

            type 'elt coq_R_bal =
            | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

            val coq_R_bal_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2

            val coq_R_bal_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2

            type 'elt coq_R_add =
            | R_add_0 of 'elt tree
            | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add
            | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

            type 'elt coq_R_remove_min =
            | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
            | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree
               * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
               * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min
               * 'elt tree * (key * 'elt)

            val coq_R_remove_min_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            val coq_R_remove_min_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            type 'elt coq_R_merge =
            | R_merge_0 of 'elt tree * 'elt tree
            | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key * 'elt) * 
               key * 'elt

            val coq_R_merge_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key ->
              'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2

            val coq_R_merge_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key ->
              'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt tree
            | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
            | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

            val coq_R_remove_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              tree -> 'a1 coq_R_remove -> 'a2

            val coq_R_remove_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              tree -> 'a1 coq_R_remove -> 'a2

            type 'elt coq_R_concat =
            | R_concat_0 of 'elt tree * 'elt tree
            | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key * 'elt)

            val coq_R_concat_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
              'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

            val coq_R_concat_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
              'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

            type 'elt coq_R_split =
            | R_split_0 of 'elt tree
            | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree

            val coq_R_split_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 ->
              'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
              coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
              -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

            val coq_R_split_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 ->
              'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
              coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
              -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

            type ('elt, 'x) coq_R_map_option =
            | R_map_option_0 of 'elt tree
            | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'x * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option
            | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option

            val coq_R_map_option_rect :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

            val coq_R_map_option_rec :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

            type ('elt, 'x0, 'x) coq_R_map2_opt =
            | R_map2_opt_0 of 'elt tree * 'x0 tree
            | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
               * 'x * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
               * ('elt, 'x0, 'x) coq_R_map2_opt
            | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
               * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
               * ('elt, 'x0, 'x) coq_R_map2_opt

            val coq_R_map2_opt_rect :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

            val coq_R_map2_opt_rec :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

            val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

            val flatten_e : 'a1 enumeration -> (key * 'a1) list
           end
         end

        type 'elt bst =
          'elt Raw.tree
          (* singleton inductive, whose constructor was Bst *)

        val this : 'a1 bst -> 'a1 Raw.tree

        type 'elt t = 'elt bst

        type key = StateProdPosOrderedType.Alt.t

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> int

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      val nullable_symb : Aut.Gram.symbol -> bool

      val nullable_word : Aut.Gram.symbol list -> bool

      val first_nterm_set : Aut.Gram.nonterminal -> TerminalSet.t

      val first_symb_set : Aut.Gram.symbol -> TerminalSet.t

      val first_word_set : Aut.Gram.symbol list -> TerminalSet.t

      val future_of_prod : Aut.Gram.production -> int -> Aut.Gram.symbol list

      val items_map : unit -> TerminalSet.t StateProdPosMap.t

      val find_items_map :
        TerminalSet.t StateProdPosMap.t -> Aut.state -> Aut.Gram.production
        -> int -> TerminalSet.t

      val forallb_items :
        TerminalSet.t StateProdPosMap.t -> (Aut.state -> Aut.Gram.production
        -> int -> TerminalSet.t -> bool) -> bool

      val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool

      val is_complete_0 : TerminalSet.t StateProdPosMap.t -> bool

      val is_complete : unit -> bool
     end

    type pt_zipper =
    | Top_ptz
    | Cons_ptl_ptz of Aut.Gram.symbol list * Aut.Gram.token list
       * Aut.GramDefs.parse_tree_list * Aut.Gram.symbol * Aut.Gram.token list
       * ptl_zipper
    and ptl_zipper =
    | Non_terminal_pt_ptlz of Aut.Gram.production * Aut.Gram.token list
       * pt_zipper
    | Cons_ptl_ptlz of Aut.Gram.symbol list * Aut.Gram.token list
       * Aut.Gram.symbol * Aut.Gram.token list * Aut.GramDefs.parse_tree
       * ptl_zipper

    val pt_zipper_rect :
      Aut.initstate -> Aut.Gram.token list -> 'a1 -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> Aut.Gram.symbol
      -> Aut.Gram.token list -> ptl_zipper -> 'a1) -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> 'a1

    val pt_zipper_rec :
      Aut.initstate -> Aut.Gram.token list -> 'a1 -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> Aut.Gram.symbol
      -> Aut.Gram.token list -> ptl_zipper -> 'a1) -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> 'a1

    val ptl_zipper_rect :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> pt_zipper -> 'a1) -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.Gram.symbol -> Aut.Gram.token list ->
      Aut.GramDefs.parse_tree -> ptl_zipper -> 'a1 -> 'a1) -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> 'a1

    val ptl_zipper_rec :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> pt_zipper -> 'a1) -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.Gram.symbol -> Aut.Gram.token list ->
      Aut.GramDefs.parse_tree -> ptl_zipper -> 'a1 -> 'a1) -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> 'a1

    type pt_dot =
    | Reduce_ptd of Aut.Gram.production * Aut.Gram.token list
       * Aut.GramDefs.parse_tree_list * pt_zipper
    | Shift_ptd of Aut.Gram.token * Aut.Gram.symbol list
       * Aut.Gram.token list * Aut.GramDefs.parse_tree_list * ptl_zipper

    val pt_dot_rect :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> pt_zipper ->
      'a1) -> (Aut.Gram.token -> Aut.Gram.symbol list -> Aut.Gram.token list
      -> Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1

    val pt_dot_rec :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> pt_zipper ->
      'a1) -> (Aut.Gram.token -> Aut.Gram.symbol list -> Aut.Gram.token list
      -> Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1

    val ptlz_sem :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> (__ -> __ arrows_right -> __) ->
      Aut.Gram.symbol_semantic_type

    val ptz_sem :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> Aut.Gram.symbol_semantic_type ->
      Aut.Gram.symbol_semantic_type

    val ptd_sem :
      Aut.initstate -> Aut.Gram.token list -> pt_dot ->
      Aut.Gram.symbol_semantic_type

    val ptlz_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> Inter.buffer

    val ptz_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      -> Aut.Gram.token list -> pt_zipper -> Inter.buffer

    val ptd_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> pt_dot ->
      Inter.buffer

    val ptlz_prod :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> Aut.Gram.production

    val ptlz_future :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> Aut.Gram.symbol list

    val ptlz_lookahead :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> Aut.Gram.terminal

    val build_pt_dot_from_pt :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree -> pt_zipper -> pt_dot

    val build_pt_dot_from_pt_rec :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> ptl_zipper ->
      pt_dot

    val build_pt_dot_from_ptl :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> ptl_zipper ->
      pt_dot

    val next_ptd :
      Aut.initstate -> Aut.Gram.token list -> pt_dot -> pt_dot option

    val next_ptd_iter :
      Aut.initstate -> Aut.Gram.token list -> pt_dot -> int -> pt_dot option

    val ptlz_cost :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> int

    val ptz_cost :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> int

    val ptd_cost : Aut.initstate -> Aut.Gram.token list -> pt_dot -> int
   end

  val complete_validator : unit -> bool

  val safe_validator : unit -> bool

  val parse :
    Aut.initstate -> int -> Inter.buffer -> Aut.Gram.symbol_semantic_type
    Inter.parse_result
 end

module Cst :
 sig
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

module Gram :
 sig
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

  val terminalNum : terminal numbered

  val coq_TerminalAlph : terminal alphabet

  type nonterminal' =
  | Coq_app_obj'nt
  | Coq_args_list'nt
  | Coq_args_obj'nt
  | Coq_obj'nt
  | Coq_prog'nt
  | Coq_rev_args_list'nt
  | Coq_simpl_obj'nt

  type nonterminal = nonterminal'

  val nonterminalNum : nonterminal numbered

  val coq_NonTerminalAlph : nonterminal alphabet

  type symbol =
  | T of terminal
  | NT of nonterminal

  val symbol_rect : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

  val symbol_rec : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

  val coq_SymbolAlph : symbol alphabet

  type terminal_semantic_type = __

  type nonterminal_semantic_type = __

  type symbol_semantic_type = __

  type token = token0

  val token_term : token -> terminal

  val token_sem : token -> symbol_semantic_type

  type production' =
  | Prod'simpl_obj'5
  | Prod'simpl_obj'4
  | Prod'simpl_obj'3
  | Prod'simpl_obj'2
  | Prod'simpl_obj'1
  | Prod'simpl_obj'0
  | Prod'rev_args_list'1
  | Prod'rev_args_list'0
  | Prod'prog'0
  | Prod'obj'2
  | Prod'obj'1
  | Prod'obj'0
  | Prod'args_obj'0
  | Prod'args_list'0
  | Prod'app_obj'1
  | Prod'app_obj'0

  type production = production'

  val productionNum : production numbered

  val coq_ProductionAlph : production alphabet

  val prod_contents :
    production -> (nonterminal * symbol list, symbol_semantic_type
    arrows_right) sigT

  val prod_lhs : production -> nonterminal

  val prod_rhs_rev : production -> symbol list

  val prod_action : production -> symbol_semantic_type arrows_right

  type parse_tree =
  | Terminal_pt of token
  | Non_terminal_pt of production * token list * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of symbol list * token list * parse_tree_list * symbol
     * token list * parse_tree

  val parse_tree_rect :
    (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1) ->
    symbol -> token list -> parse_tree -> 'a1

  val parse_tree_rec :
    (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1) ->
    symbol -> token list -> parse_tree -> 'a1

  val parse_tree_list_rect :
    'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol ->
    token list -> parse_tree -> 'a1) -> symbol list -> token list ->
    parse_tree_list -> 'a1

  val parse_tree_list_rec :
    'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol ->
    token list -> parse_tree -> 'a1) -> symbol list -> token list ->
    parse_tree_list -> 'a1

  val pt_sem : symbol -> token list -> parse_tree -> symbol_semantic_type

  val ptl_sem :
    symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1

  val pt_size : symbol -> token list -> parse_tree -> int

  val ptl_size : symbol list -> token list -> parse_tree_list -> int
 end
module Coq__1 : module type of struct include Gram end

module Aut :
 sig
  module Gram :
   sig
    type terminal' = Gram.terminal' =
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

    val terminalNum : terminal numbered

    val coq_TerminalAlph : terminal alphabet

    type nonterminal' = Gram.nonterminal' =
    | Coq_app_obj'nt
    | Coq_args_list'nt
    | Coq_args_obj'nt
    | Coq_obj'nt
    | Coq_prog'nt
    | Coq_rev_args_list'nt
    | Coq_simpl_obj'nt

    type nonterminal = nonterminal'

    val nonterminalNum : nonterminal numbered

    val coq_NonTerminalAlph : nonterminal alphabet

    type symbol = Gram.symbol =
    | T of terminal
    | NT of nonterminal

    val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

    val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

    val coq_SymbolAlph : symbol alphabet

    type terminal_semantic_type = __

    type nonterminal_semantic_type = __

    type symbol_semantic_type = __

    type token = token0

    val token_term : token -> terminal

    val token_sem : token -> symbol_semantic_type

    type production' = Gram.production' =
    | Prod'simpl_obj'5
    | Prod'simpl_obj'4
    | Prod'simpl_obj'3
    | Prod'simpl_obj'2
    | Prod'simpl_obj'1
    | Prod'simpl_obj'0
    | Prod'rev_args_list'1
    | Prod'rev_args_list'0
    | Prod'prog'0
    | Prod'obj'2
    | Prod'obj'1
    | Prod'obj'0
    | Prod'args_obj'0
    | Prod'args_list'0
    | Prod'app_obj'1
    | Prod'app_obj'0

    type production = production'

    val productionNum : production numbered

    val coq_ProductionAlph : production alphabet

    val prod_contents :
      production -> (nonterminal * symbol list, symbol_semantic_type
      arrows_right) sigT

    val prod_lhs : production -> nonterminal

    val prod_rhs_rev : production -> symbol list

    val prod_action : production -> symbol_semantic_type arrows_right

    type parse_tree = Gram.parse_tree =
    | Terminal_pt of token
    | Non_terminal_pt of production * token list * parse_tree_list
    and parse_tree_list = Gram.parse_tree_list =
    | Nil_ptl
    | Cons_ptl of symbol list * token list * parse_tree_list * symbol
       * token list * parse_tree

    val parse_tree_rect :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1

    val parse_tree_rec :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1

    val parse_tree_list_rect :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1

    val parse_tree_list_rec :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1

    val pt_sem : symbol -> token list -> parse_tree -> symbol_semantic_type

    val ptl_sem :
      symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1

    val pt_size : symbol -> token list -> parse_tree -> int

    val ptl_size : symbol list -> token list -> parse_tree_list -> int
   end

  module GramDefs :
   sig
    type terminal' = Coq__1.terminal' =
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

    val terminalNum : terminal numbered

    val coq_TerminalAlph : terminal alphabet

    type nonterminal' = Coq__1.nonterminal' =
    | Coq_app_obj'nt
    | Coq_args_list'nt
    | Coq_args_obj'nt
    | Coq_obj'nt
    | Coq_prog'nt
    | Coq_rev_args_list'nt
    | Coq_simpl_obj'nt

    type nonterminal = nonterminal'

    val nonterminalNum : nonterminal numbered

    val coq_NonTerminalAlph : nonterminal alphabet

    type symbol = Coq__1.symbol =
    | T of terminal
    | NT of nonterminal

    val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

    val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1

    val coq_SymbolAlph : symbol alphabet

    type terminal_semantic_type = __

    type nonterminal_semantic_type = __

    type symbol_semantic_type = __

    type token = token0

    val token_term : token -> terminal

    val token_sem : token -> symbol_semantic_type

    type production' = Coq__1.production' =
    | Prod'simpl_obj'5
    | Prod'simpl_obj'4
    | Prod'simpl_obj'3
    | Prod'simpl_obj'2
    | Prod'simpl_obj'1
    | Prod'simpl_obj'0
    | Prod'rev_args_list'1
    | Prod'rev_args_list'0
    | Prod'prog'0
    | Prod'obj'2
    | Prod'obj'1
    | Prod'obj'0
    | Prod'args_obj'0
    | Prod'args_list'0
    | Prod'app_obj'1
    | Prod'app_obj'0

    type production = production'

    val productionNum : production numbered

    val coq_ProductionAlph : production alphabet

    val prod_contents :
      production -> (nonterminal * symbol list, symbol_semantic_type
      arrows_right) sigT

    val prod_lhs : production -> nonterminal

    val prod_rhs_rev : production -> symbol list

    val prod_action : production -> symbol_semantic_type arrows_right

    type parse_tree = Coq__1.parse_tree =
    | Terminal_pt of token
    | Non_terminal_pt of production * token list * parse_tree_list
    and parse_tree_list = Coq__1.parse_tree_list =
    | Nil_ptl
    | Cons_ptl of symbol list * token list * parse_tree_list * symbol
       * token list * parse_tree

    val parse_tree_rect :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1

    val parse_tree_rec :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1

    val parse_tree_list_rect :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1

    val parse_tree_list_rec :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1

    val pt_sem : symbol -> token list -> parse_tree -> symbol_semantic_type

    val ptl_sem :
      symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1

    val pt_size : symbol -> token list -> parse_tree -> int

    val ptl_size : symbol list -> token list -> parse_tree_list -> int
   end

  val nullable_nterm : Coq__1.nonterminal -> bool

  val first_nterm : Coq__1.nonterminal -> Coq__1.terminal list

  type noninitstate' =
  | Nis'32
  | Nis'31
  | Nis'29
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

  val noninitstateNum : noninitstate numbered

  val coq_NonInitStateAlph : noninitstate alphabet

  val last_symb_of_non_init_state : noninitstate -> Coq__1.symbol

  type initstate' =
  | Init'0

  type initstate = initstate'

  val initstateNum : initstate numbered

  val coq_InitStateAlph : initstate alphabet

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

  val start_nt : initstate -> Coq__1.nonterminal

  val action_table : state -> action

  val goto_table : state -> Coq__1.nonterminal -> noninitstate option

  val past_symb_of_non_init_state : noninitstate -> Coq__1.symbol list

  val past_state_of_non_init_state : noninitstate -> (state -> bool) list

  val items_of_state : state -> item list

  val coq_N_of_state : state -> n
 end

module MenhirLibParser :
 sig
  module Inter :
   sig
    module ValidSafe :
     sig
      val singleton_state_pred : Aut.state -> Aut.state -> bool

      val past_state_of_state : Aut.state -> (Aut.state -> bool) list

      val head_symbs_of_state : Aut.state -> Aut.Gram.symbol list

      val head_states_of_state : Aut.state -> (Aut.state -> bool) list

      val is_prefix : Aut.Gram.symbol list -> Aut.Gram.symbol list -> bool

      val is_prefix_pred :
        (Aut.state -> bool) list -> (Aut.state -> bool) list -> bool

      val is_state_valid_after_pop :
        Aut.state -> Aut.Gram.symbol list -> (Aut.state -> bool) list -> bool

      val is_safe : unit -> bool
     end

    type coq_Decidable = bool

    val decide : coq_Decidable -> bool

    val comparable_decidable_eq :
      'a1 comparable -> 'a1 -> 'a1 -> coq_Decidable

    val list_decidable_eq :
      ('a1 -> 'a1 -> coq_Decidable) -> 'a1 list -> 'a1 list -> coq_Decidable

    val cast : 'a1 -> 'a1 -> (unit -> coq_Decidable) -> 'a2 -> 'a2

    type buffer = __buffer Lazy.t
    and __buffer =
    | Buf_cons of Aut.Gram.token * buffer

    val buf_head : buffer -> Aut.Gram.token

    val buf_tail : buffer -> buffer

    val app_buf : Aut.Gram.token list -> buffer -> buffer

    type noninitstate_type = Aut.Gram.symbol_semantic_type

    type stack = (Aut.noninitstate, noninitstate_type) sigT list

    val state_of_stack : Aut.initstate -> stack -> Aut.state

    val state_stack_of_stack :
      Aut.initstate -> stack -> (Aut.state -> bool) list

    val symb_stack_of_stack : stack -> Aut.Gram.symbol list

    val pop : Aut.Gram.symbol list -> stack -> 'a1 arrows_right -> stack * 'a1

    type step_result =
    | Fail_sr_full of Aut.state * Aut.Gram.token
    | Accept_sr of Aut.Gram.symbol_semantic_type * buffer
    | Progress_sr of stack * buffer

    val step_result_rect :
      Aut.initstate -> (Aut.state -> Aut.Gram.token -> 'a1) ->
      (Aut.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
      'a1) -> step_result -> 'a1

    val step_result_rec :
      Aut.initstate -> (Aut.state -> Aut.Gram.token -> 'a1) ->
      (Aut.Gram.symbol_semantic_type -> buffer -> 'a1) -> (stack -> buffer ->
      'a1) -> step_result -> 'a1

    val reduce_step :
      Aut.initstate -> stack -> Aut.Gram.production -> buffer -> step_result

    val step : Aut.initstate -> stack -> buffer -> step_result

    val parse_fix : Aut.initstate -> stack -> buffer -> int -> step_result

    type 'a parse_result =
    | Fail_pr_full of Aut.state * Aut.Gram.token
    | Timeout_pr
    | Parsed_pr of 'a * buffer

    val parse_result_rect :
      (Aut.state -> Aut.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2)
      -> 'a1 parse_result -> 'a2

    val parse_result_rec :
      (Aut.state -> Aut.Gram.token -> 'a2) -> 'a2 -> ('a1 -> buffer -> 'a2)
      -> 'a1 parse_result -> 'a2

    val parse :
      Aut.initstate -> buffer -> int -> Aut.Gram.symbol_semantic_type
      parse_result
   end

  module Correct :
   sig
   end

  module Complete :
   sig
    module Valid :
     sig
      module TerminalComparableM :
       sig
        type t = Aut.Gram.terminal

        val tComparable : t comparable
       end

      module TerminalOrderedType :
       sig
        module Alt :
         sig
          type t = TerminalComparableM.t

          val compare : t -> t -> comparison
         end

        type t = Alt.t

        val compare : Alt.t -> Alt.t -> Alt.t compare0

        val eq_dec : Alt.t -> Alt.t -> bool
       end

      module StateProdPosComparableM :
       sig
        type t = (Aut.state * Aut.Gram.production) * int

        val tComparable : t comparable
       end

      module StateProdPosOrderedType :
       sig
        module Alt :
         sig
          type t = StateProdPosComparableM.t

          val compare : t -> t -> comparison
         end

        type t = Alt.t

        val compare : Alt.t -> Alt.t -> Alt.t compare0

        val eq_dec : Alt.t -> Alt.t -> bool
       end

      module TerminalSet :
       sig
        module X' :
         sig
          type t = TerminalOrderedType.Alt.t

          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison
         end

        module MSet :
         sig
          module Raw :
           sig
            type elt = TerminalOrderedType.Alt.t

            type tree =
            | Leaf
            | Node of Z_as_Int.t * tree * TerminalOrderedType.Alt.t * tree

            val empty : tree

            val is_empty : tree -> bool

            val mem : TerminalOrderedType.Alt.t -> tree -> bool

            val min_elt : tree -> elt option

            val max_elt : tree -> elt option

            val choose : tree -> elt option

            val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

            val elements_aux :
              TerminalOrderedType.Alt.t list -> tree ->
              TerminalOrderedType.Alt.t list

            val elements : tree -> TerminalOrderedType.Alt.t list

            val rev_elements_aux :
              TerminalOrderedType.Alt.t list -> tree ->
              TerminalOrderedType.Alt.t list

            val rev_elements : tree -> TerminalOrderedType.Alt.t list

            val cardinal : tree -> int

            val maxdepth : tree -> int

            val mindepth : tree -> int

            val for_all : (elt -> bool) -> tree -> bool

            val exists_ : (elt -> bool) -> tree -> bool

            type enumeration =
            | End
            | More of elt * tree * enumeration

            val cons : tree -> enumeration -> enumeration

            val compare_more :
              TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
              enumeration -> comparison

            val compare_cont :
              tree -> (enumeration -> comparison) -> enumeration -> comparison

            val compare_end : enumeration -> comparison

            val compare : tree -> tree -> comparison

            val equal : tree -> tree -> bool

            val subsetl :
              (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

            val subsetr :
              (tree -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool

            val subset : tree -> tree -> bool

            type t = tree

            val height : t -> Z_as_Int.t

            val singleton : TerminalOrderedType.Alt.t -> tree

            val create : t -> TerminalOrderedType.Alt.t -> t -> tree

            val assert_false : t -> TerminalOrderedType.Alt.t -> t -> tree

            val bal : t -> TerminalOrderedType.Alt.t -> t -> tree

            val add : TerminalOrderedType.Alt.t -> tree -> tree

            val join : tree -> elt -> t -> t

            val remove_min : tree -> elt -> t -> t * elt

            val merge : tree -> tree -> tree

            val remove : TerminalOrderedType.Alt.t -> tree -> tree

            val concat : tree -> tree -> tree

            type triple = { t_left : t; t_in : bool; t_right : t }

            val t_left : triple -> t

            val t_in : triple -> bool

            val t_right : triple -> t

            val split : TerminalOrderedType.Alt.t -> tree -> triple

            val inter : tree -> tree -> tree

            val diff : tree -> tree -> tree

            val union : tree -> tree -> tree

            val filter : (elt -> bool) -> tree -> tree

            val partition : (elt -> bool) -> t -> t * t

            val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool

            val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool

            val isok : tree -> bool

            module MX :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = TerminalOrderedType.Alt.t

                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison

                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end

                module TO :
                 sig
                  type t = TerminalOrderedType.Alt.t

                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison

                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
               end

              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool

              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
             end

            type coq_R_min_elt =
            | R_min_elt_0 of tree
            | R_min_elt_1 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_min_elt_2 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * elt option * coq_R_min_elt

            type coq_R_max_elt =
            | R_max_elt_0 of tree
            | R_max_elt_1 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_max_elt_2 of tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * elt option * coq_R_max_elt

            module L :
             sig
              module MO :
               sig
                module OrderTac :
                 sig
                  module OTF :
                   sig
                    type t = TerminalOrderedType.Alt.t

                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison

                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end

                  module TO :
                   sig
                    type t = TerminalOrderedType.Alt.t

                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison

                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end
                 end

                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool

                val lt_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool

                val eqb :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end

            val flatten_e : enumeration -> elt list

            type coq_R_bal =
            | R_bal_0 of t * TerminalOrderedType.Alt.t * t
            | R_bal_1 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_2 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_3 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree
            | R_bal_4 of t * TerminalOrderedType.Alt.t * t
            | R_bal_5 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_6 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree
            | R_bal_7 of t * TerminalOrderedType.Alt.t * t * Z_as_Int.t
               * tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * 
               tree * TerminalOrderedType.Alt.t * tree
            | R_bal_8 of t * TerminalOrderedType.Alt.t * t

            type coq_R_remove_min =
            | R_remove_min_0 of tree * elt * t
            | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * (t * elt)
               * coq_R_remove_min * t * elt

            type coq_R_merge =
            | R_merge_0 of tree * tree
            | R_merge_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_merge_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * elt

            type coq_R_concat =
            | R_concat_0 of tree * tree
            | R_concat_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_concat_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * elt

            type coq_R_inter =
            | R_inter_0 of tree * tree
            | R_inter_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_inter_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_inter * tree * coq_R_inter
            | R_inter_3 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_inter * tree * coq_R_inter

            type coq_R_diff =
            | R_diff_0 of tree * tree
            | R_diff_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_diff_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_diff * tree * coq_R_diff
            | R_diff_3 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_diff * tree * coq_R_diff

            type coq_R_union =
            | R_union_0 of tree * tree
            | R_union_1 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree
            | R_union_2 of tree * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.t * tree
               * TerminalOrderedType.Alt.t * tree * t * bool * t * tree
               * coq_R_union * tree * coq_R_union
           end

          module E :
           sig
            type t = TerminalOrderedType.Alt.t

            val compare :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              comparison

            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end

          type elt = TerminalOrderedType.Alt.t

          type t_ = Raw.t
            (* singleton inductive, whose constructor was Mkt *)

          val this : t_ -> Raw.t

          type t = t_

          val mem : elt -> t -> bool

          val add : elt -> t -> t

          val remove : elt -> t -> t

          val singleton : elt -> t

          val union : t -> t -> t

          val inter : t -> t -> t

          val diff : t -> t -> t

          val equal : t -> t -> bool

          val subset : t -> t -> bool

          val empty : t

          val is_empty : t -> bool

          val elements : t -> elt list

          val choose : t -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

          val cardinal : t -> int

          val filter : (elt -> bool) -> t -> t

          val for_all : (elt -> bool) -> t -> bool

          val exists_ : (elt -> bool) -> t -> bool

          val partition : (elt -> bool) -> t -> t * t

          val eq_dec : t -> t -> bool

          val compare : t -> t -> comparison

          val min_elt : t -> elt option

          val max_elt : t -> elt option
         end

        type elt = TerminalOrderedType.Alt.t

        type t = MSet.t

        val empty : t

        val is_empty : t -> bool

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val singleton : elt -> t

        val remove : elt -> t -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val eq_dec : t -> t -> bool

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val filter : (elt -> bool) -> t -> t

        val partition : (elt -> bool) -> t -> t * t

        val cardinal : t -> int

        val elements : t -> elt list

        val choose : t -> elt option

        module MF :
         sig
          val eqb :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end

        val min_elt : t -> elt option

        val max_elt : t -> elt option

        val compare : t -> t -> t compare0

        module E :
         sig
          type t = TerminalOrderedType.Alt.t

          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            TerminalOrderedType.Alt.t compare0

          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
       end

      module StateProdPosMap :
       sig
        module E :
         sig
          type t = StateProdPosOrderedType.Alt.t

          val compare :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            StateProdPosOrderedType.Alt.t compare0

          val eq_dec :
            StateProdPosOrderedType.Alt.t -> StateProdPosOrderedType.Alt.t ->
            bool
         end

        module Raw :
         sig
          type key = StateProdPosOrderedType.Alt.t

          type 'elt tree =
          | Leaf
          | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

          val tree_rect :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val tree_rec :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val height : 'a1 tree -> Z_as_Int.t

          val cardinal : 'a1 tree -> int

          val empty : 'a1 tree

          val is_empty : 'a1 tree -> bool

          val mem : StateProdPosOrderedType.Alt.t -> 'a1 tree -> bool

          val find : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option

          val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

          val remove_min :
            'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

          val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

          val remove : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree

          val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                               t_right : 'elt tree }

          val t_left : 'a1 triple -> 'a1 tree

          val t_opt : 'a1 triple -> 'a1 option

          val t_right : 'a1 triple -> 'a1 tree

          val split : StateProdPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple

          val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

          val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

          val elements : 'a1 tree -> (key * 'a1) list

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          type 'elt enumeration =
          | End
          | More of key * 'elt * 'elt tree * 'elt enumeration

          val enumeration_rect :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val enumeration_rec :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

          val equal_more :
            ('a1 -> 'a1 -> bool) -> StateProdPosOrderedType.Alt.t -> 'a1 ->
            ('a1 enumeration -> bool) -> 'a1 enumeration -> bool

          val equal_cont :
            ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
            'a1 enumeration -> bool

          val equal_end : 'a1 enumeration -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

          val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

          val map2_opt :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3
            tree

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree
            -> 'a3 tree

          module Proofs :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = StateProdPosOrderedType.Alt.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val lt_dec :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool

              val eqb :
                StateProdPosOrderedType.Alt.t ->
                StateProdPosOrderedType.Alt.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = StateProdPosOrderedType.Alt.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end
             end

            module L :
             sig
              module MX :
               sig
                module TO :
                 sig
                  type t = StateProdPosOrderedType.Alt.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val lt_dec :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool

                val eqb :
                  StateProdPosOrderedType.Alt.t ->
                  StateProdPosOrderedType.Alt.t -> bool
               end

              module PX :
               sig
                module MO :
                 sig
                  module TO :
                   sig
                    type t = StateProdPosOrderedType.Alt.t
                   end

                  module IsTO :
                   sig
                   end

                  module OrderTac :
                   sig
                   end

                  val eq_dec :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool

                  val lt_dec :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool

                  val eqb :
                    StateProdPosOrderedType.Alt.t ->
                    StateProdPosOrderedType.Alt.t -> bool
                 end
               end

              type key = StateProdPosOrderedType.Alt.t

              type 'elt t = (StateProdPosOrderedType.Alt.t * 'elt) list

              val empty : 'a1 t

              val is_empty : 'a1 t -> bool

              val mem : key -> 'a1 t -> bool

              type 'elt coq_R_mem =
              | R_mem_0 of 'elt t
              | R_mem_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_mem_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_mem_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
                 * 'elt coq_R_mem

              val coq_R_mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
                'a1 coq_R_mem -> 'a2

              val coq_R_mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
                'a1 coq_R_mem -> 'a2

              val mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

              val find : key -> 'a1 t -> 'a1 option

              type 'elt coq_R_find =
              | R_find_0 of 'elt t
              | R_find_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_find_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_find_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
                 * 'elt option * 'elt coq_R_find

              val coq_R_find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 option -> 'a1 coq_R_find -> 'a2

              val coq_R_find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 option -> 'a1 coq_R_find -> 'a2

              val find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val coq_R_find_correct :
                key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

              val add : key -> 'a1 -> 'a1 t -> 'a1 t

              type 'elt coq_R_add =
              | R_add_0 of 'elt t
              | R_add_1 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_add_2 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_add_3 of 'elt t * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list * 'elt t
                 * 'elt coq_R_add

              val coq_R_add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
                'a1 coq_R_add -> 'a2

              val coq_R_add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
                'a1 coq_R_add -> 'a2

              val add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val coq_R_add_correct :
                key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

              val remove : key -> 'a1 t -> 'a1 t

              type 'elt coq_R_remove =
              | R_remove_0 of 'elt t
              | R_remove_1 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_remove_2 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
              | R_remove_3 of 'elt t * StateProdPosOrderedType.Alt.t * 
                 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list * 
                 'elt t * 'elt coq_R_remove

              val coq_R_remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
                -> 'a1 coq_R_remove -> 'a2

              val coq_R_remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
                -> 'a1 coq_R_remove -> 'a2

              val remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> 'a1 t -> 'a2

              val coq_R_remove_correct :
                key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

              val elements : 'a1 t -> 'a1 t

              val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

              type ('elt, 'a) coq_R_fold =
              | R_fold_0 of 'elt t * 'a
              | R_fold_1 of 'elt t * 'a * StateProdPosOrderedType.Alt.t
                 * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list * 
                 'a * ('elt, 'a) coq_R_fold

              val coq_R_fold_rect :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 ->
                ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
                -> ('a1, 'a2) coq_R_fold -> 'a3

              val coq_R_fold_rec :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a2 ->
                ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
                -> ('a1, 'a2) coq_R_fold -> 'a3

              val fold_rect :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a3 ->
                'a3) -> 'a1 t -> 'a2 -> 'a3

              val fold_rec :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> 'a3 ->
                'a3) -> 'a1 t -> 'a2 -> 'a3

              val coq_R_fold_correct :
                (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold

              val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

              type 'elt coq_R_equal =
              | R_equal_0 of 'elt t * 'elt t
              | R_equal_1 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
                 * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
                 * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list * bool
                 * 'elt coq_R_equal
              | R_equal_2 of 'elt t * 'elt t * StateProdPosOrderedType.Alt.t
                 * 'elt * (StateProdPosOrderedType.Alt.t * 'elt) list
                 * StateProdPosOrderedType.Alt.t * 'elt
                 * (StateProdPosOrderedType.Alt.t * 'elt) list
                 * StateProdPosOrderedType.Alt.t compare0
              | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

              val coq_R_equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
                -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

              val coq_R_equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
                -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

              val equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> 'a2

              val equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t -> 'a1 ->
                (StateProdPosOrderedType.Alt.t * 'a1) list -> __ ->
                StateProdPosOrderedType.Alt.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> 'a2

              val coq_R_equal_correct :
                ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal

              val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

              val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

              val option_cons :
                key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

              val map2_l :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

              val map2_r :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

              val map2 :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                'a3 t

              val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

              val fold_right_pair :
                ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

              val map2_alt :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                (key * 'a3) list

              val at_least_one :
                'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

              val at_least_one_then_f :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
                option -> 'a3 option
             end

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt tree
            | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem
            | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem
              -> 'a2

            val coq_R_mem_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem
              -> 'a2

            type 'elt coq_R_find =
            | R_find_0 of 'elt tree
            | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find
            | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              option -> 'a1 coq_R_find -> 'a2

            val coq_R_find_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              option -> 'a1 coq_R_find -> 'a2

            type 'elt coq_R_bal =
            | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

            val coq_R_bal_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2

            val coq_R_bal_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2

            type 'elt coq_R_add =
            | R_add_0 of 'elt tree
            | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add
            | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

            type 'elt coq_R_remove_min =
            | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
            | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree
               * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
               * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min
               * 'elt tree * (key * 'elt)

            val coq_R_remove_min_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            val coq_R_remove_min_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            type 'elt coq_R_merge =
            | R_merge_0 of 'elt tree * 'elt tree
            | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key * 'elt) * 
               key * 'elt

            val coq_R_merge_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key ->
              'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2

            val coq_R_merge_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key ->
              'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt tree
            | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
            | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

            val coq_R_remove_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              tree -> 'a1 coq_R_remove -> 'a2

            val coq_R_remove_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
              tree -> 'a1 coq_R_remove -> 'a2

            type 'elt coq_R_concat =
            | R_concat_0 of 'elt tree * 'elt tree
            | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key * 'elt)

            val coq_R_concat_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
              'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

            val coq_R_concat_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
              'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

            type 'elt coq_R_split =
            | R_split_0 of 'elt tree
            | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree

            val coq_R_split_rect :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 ->
              'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
              coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
              -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

            val coq_R_split_rec :
              StateProdPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 ->
              'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
              coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
              -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

            type ('elt, 'x) coq_R_map_option =
            | R_map_option_0 of 'elt tree
            | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'x * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option
            | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option

            val coq_R_map_option_rect :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

            val coq_R_map_option_rec :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

            type ('elt, 'x0, 'x) coq_R_map2_opt =
            | R_map2_opt_0 of 'elt tree * 'x0 tree
            | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t
            | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
               * 'x * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
               * ('elt, 'x0, 'x) coq_R_map2_opt
            | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
               * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
               * ('elt, 'x0, 'x) coq_R_map2_opt

            val coq_R_map2_opt_rect :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

            val coq_R_map2_opt_rec :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

            val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

            val flatten_e : 'a1 enumeration -> (key * 'a1) list
           end
         end

        type 'elt bst =
          'elt Raw.tree
          (* singleton inductive, whose constructor was Bst *)

        val this : 'a1 bst -> 'a1 Raw.tree

        type 'elt t = 'elt bst

        type key = StateProdPosOrderedType.Alt.t

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> int

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      val nullable_symb : Aut.Gram.symbol -> bool

      val nullable_word : Aut.Gram.symbol list -> bool

      val first_nterm_set : Aut.Gram.nonterminal -> TerminalSet.t

      val first_symb_set : Aut.Gram.symbol -> TerminalSet.t

      val first_word_set : Aut.Gram.symbol list -> TerminalSet.t

      val future_of_prod : Aut.Gram.production -> int -> Aut.Gram.symbol list

      val items_map : unit -> TerminalSet.t StateProdPosMap.t

      val find_items_map :
        TerminalSet.t StateProdPosMap.t -> Aut.state -> Aut.Gram.production
        -> int -> TerminalSet.t

      val forallb_items :
        TerminalSet.t StateProdPosMap.t -> (Aut.state -> Aut.Gram.production
        -> int -> TerminalSet.t -> bool) -> bool

      val is_end_reduce : TerminalSet.t StateProdPosMap.t -> bool

      val is_complete_0 : TerminalSet.t StateProdPosMap.t -> bool

      val is_complete : unit -> bool
     end

    type pt_zipper =
    | Top_ptz
    | Cons_ptl_ptz of Aut.Gram.symbol list * Aut.Gram.token list
       * Aut.GramDefs.parse_tree_list * Aut.Gram.symbol * Aut.Gram.token list
       * ptl_zipper
    and ptl_zipper =
    | Non_terminal_pt_ptlz of Aut.Gram.production * Aut.Gram.token list
       * pt_zipper
    | Cons_ptl_ptlz of Aut.Gram.symbol list * Aut.Gram.token list
       * Aut.Gram.symbol * Aut.Gram.token list * Aut.GramDefs.parse_tree
       * ptl_zipper

    val pt_zipper_rect :
      Aut.initstate -> Aut.Gram.token list -> 'a1 -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> Aut.Gram.symbol
      -> Aut.Gram.token list -> ptl_zipper -> 'a1) -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> 'a1

    val pt_zipper_rec :
      Aut.initstate -> Aut.Gram.token list -> 'a1 -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> Aut.Gram.symbol
      -> Aut.Gram.token list -> ptl_zipper -> 'a1) -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> 'a1

    val ptl_zipper_rect :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> pt_zipper -> 'a1) -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.Gram.symbol -> Aut.Gram.token list ->
      Aut.GramDefs.parse_tree -> ptl_zipper -> 'a1 -> 'a1) -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> 'a1

    val ptl_zipper_rec :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> pt_zipper -> 'a1) -> (Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.Gram.symbol -> Aut.Gram.token list ->
      Aut.GramDefs.parse_tree -> ptl_zipper -> 'a1 -> 'a1) -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> 'a1

    type pt_dot =
    | Reduce_ptd of Aut.Gram.production * Aut.Gram.token list
       * Aut.GramDefs.parse_tree_list * pt_zipper
    | Shift_ptd of Aut.Gram.token * Aut.Gram.symbol list
       * Aut.Gram.token list * Aut.GramDefs.parse_tree_list * ptl_zipper

    val pt_dot_rect :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> pt_zipper ->
      'a1) -> (Aut.Gram.token -> Aut.Gram.symbol list -> Aut.Gram.token list
      -> Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1

    val pt_dot_rec :
      Aut.initstate -> Aut.Gram.token list -> (Aut.Gram.production ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> pt_zipper ->
      'a1) -> (Aut.Gram.token -> Aut.Gram.symbol list -> Aut.Gram.token list
      -> Aut.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1

    val ptlz_sem :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> (__ -> __ arrows_right -> __) ->
      Aut.Gram.symbol_semantic_type

    val ptz_sem :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> Aut.Gram.symbol_semantic_type ->
      Aut.Gram.symbol_semantic_type

    val ptd_sem :
      Aut.initstate -> Aut.Gram.token list -> pt_dot ->
      Aut.Gram.symbol_semantic_type

    val ptlz_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> Inter.buffer

    val ptz_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      -> Aut.Gram.token list -> pt_zipper -> Inter.buffer

    val ptd_buffer :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> pt_dot ->
      Inter.buffer

    val ptlz_prod :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> Aut.Gram.production

    val ptlz_future :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> Aut.Gram.symbol list

    val ptlz_lookahead :
      Aut.initstate -> Aut.Gram.token list -> Inter.buffer -> Aut.Gram.symbol
      list -> Aut.Gram.token list -> ptl_zipper -> Aut.Gram.terminal

    val build_pt_dot_from_pt :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree -> pt_zipper -> pt_dot

    val build_pt_dot_from_pt_rec :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> ptl_zipper ->
      pt_dot

    val build_pt_dot_from_ptl :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> Aut.GramDefs.parse_tree_list -> ptl_zipper ->
      pt_dot

    val next_ptd :
      Aut.initstate -> Aut.Gram.token list -> pt_dot -> pt_dot option

    val next_ptd_iter :
      Aut.initstate -> Aut.Gram.token list -> pt_dot -> int -> pt_dot option

    val ptlz_cost :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol list ->
      Aut.Gram.token list -> ptl_zipper -> int

    val ptz_cost :
      Aut.initstate -> Aut.Gram.token list -> Aut.Gram.symbol ->
      Aut.Gram.token list -> pt_zipper -> int

    val ptd_cost : Aut.initstate -> Aut.Gram.token list -> pt_dot -> int
   end

  val complete_validator : unit -> bool

  val safe_validator : unit -> bool

  val parse :
    Aut.initstate -> int -> Inter.buffer -> Aut.Gram.symbol_semantic_type
    Inter.parse_result
 end

val prog :
  int -> MenhirLibParser.Inter.buffer -> Cst.obj
  MenhirLibParser.Inter.parse_result
