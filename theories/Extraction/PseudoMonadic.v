From Coq Require Extraction.

(** We cannot use class based generalization for
    the following definitions as Coq does not support
    extractable polymorphism across [Prop] and [Set].
    #See <a href="https://github.com/coq/coq/issues/19452">this Coq issue</a># *)

Definition sumbool_failable_bind {A B} (ab : {A} + {B}) {C D : Prop} (fail : B -> D) (next : A -> {C} + {D}) :=
  match ab with
  | left a => next a
  | right b => right (fail b)
  end.
Transparent sumbool_failable_bind.
Arguments sumbool_failable_bind /.

Notation "'let*b' a ':=' ab 'while' fail 'in' next" := (sumbool_failable_bind ab fail (fun a => next)) (at level 0, a pattern, next at level 10, right associativity, only parsing).
Notation "'pureb' a" := (left a) (at level 0, only parsing).

Definition sumor_failable_bind {A B} (ab : A + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> C + {D}) :=
  match ab with
  | inleft a => next a
  | inright b => inright (fail b)
  end.
Transparent sumor_failable_bind.
Arguments sumor_failable_bind /.

Notation "'let*o' a ':=' ab 'while' fail 'in' next" := (sumor_failable_bind ab fail (fun a => next)) (at level 0, a pattern, next at level 10, right associativity, only parsing).
Notation "'pureo' a" := (inleft a) (at level 0, only parsing).

Definition sumbool_sumor_failable_bind {A B} (ab : {A} + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> C + {D}) :=
  match ab with
  | left a => next a
  | right b => inright (fail b)
  end.
Transparent sumbool_sumor_failable_bind.
Arguments sumbool_sumor_failable_bind /.

Notation "'let*b->o' a ':=' ab 'while' fail 'in' next" := (sumbool_sumor_failable_bind ab fail (fun a => next)) (at level 0, a pattern, next at level 10, right associativity, only parsing).

Definition sumor_sumbool_failable_bind {A B} (ab : A + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> {C} + {D}) :=
  match ab with
  | inleft a => next a
  | inright b => right (fail b)
  end.
Transparent sumor_sumbool_failable_bind.
Arguments sumor_sumbool_failable_bind /.

Notation "'let*o->b' a ':=' ab 'while' fail 'in' next" := (sumor_sumbool_failable_bind ab fail (fun a => next)) (at level 0, a pattern, next at level 10, right associativity, only parsing).

Extraction Inline sumbool_failable_bind sumor_failable_bind sumbool_sumor_failable_bind sumor_sumbool_failable_bind.
