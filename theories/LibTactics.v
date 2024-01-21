From Coq Require Export Program.Tactics Lia.

Create HintDb mcltt discriminated.

(** Generalization of Variables *)

Tactic Notation "gen" ident(x) := generalize dependent x.
Tactic Notation "gen" ident(x) ident(y) := gen x; gen y.
Tactic Notation "gen" ident(x) ident(y) ident(z) := gen x y; gen z.
Tactic Notation "gen" ident(x) ident(y) ident(z) ident(w) := gen x y z; gen w.

(** Marking-based Tactics *)

Definition __mark__ A (a : A) : A := a.
Arguments __mark__ {A} a : simpl never.

Ltac mark H :=
  let t := type of H in
  fold (__mark__ t) in H.
Ltac unmark H := unfold __mark__ in H.

Ltac mark_all :=
  repeat match goal with [H: ?P |- _] =>
    try (match P with __mark__ _ => fail 2 end); mark H
  end.
Ltac unmark_all := unfold __mark__ in *.

Ltac on_all_marked_hyp tac :=
  match goal with
  | [ H : __mark__ ?A |- _ ] => unmark H; tac H; on_all_marked_hyp tac; mark H
  | _ => idtac
  end.
Tactic Notation "on_all_marked_hyp:" tactic4(tac) := on_all_marked_hyp tac.
Tactic Notation "on_all_hyp:" tactic4(tac) :=
  mark_all; (on_all_marked_hyp: tac); unmark_all.

(** Simple helper *)

Ltac destruct_logic :=
  destruct_one_pair
  || destruct_one_ex
  || match goal with
    | [ H : ?X \/ ?Y |- _ ] => destruct H
    | [ ev : { _ } + { _ } |- _ ] => destruct ev
    | [ ev : _ + { _ } |- _ ] => destruct ev
    | [ ev : _ + _ |- _ ] => destruct ev
    end.

Ltac destruct_all := repeat destruct_logic.

(** McLTT automation *)

Tactic Notation "mauto" :=
  eauto with mcltt core.

Tactic Notation "mauto" int_or_var(pow) :=
  eauto pow with mcltt core.

Tactic Notation "mauto" "using" uconstr(use) :=
  eauto using use with mcltt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) :=
  eauto using use1, use2 with mcltt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) :=
  eauto using use1, use2, use3 with mcltt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) "," uconstr(use4) :=
  eauto using use1, use2, use3, use4 with mcltt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use) :=
  eauto pow using use with mcltt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) :=
  eauto pow using use1, use2 with mcltt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) "," uconstr(use4) :=
  eauto pow using use1, use2, use3, use4 with mcltt core.
