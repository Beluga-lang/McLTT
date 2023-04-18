Require Export Coq.Program.Tactics.

Require Export Lia.

Create HintDb mcltt discriminated.

(** Generalization of Variables *)

Tactic Notation "gen" ident(x) := generalize dependent x.
Tactic Notation "gen" ident(x) ident(y) := gen x; gen y.
Tactic Notation "gen" ident(x) ident(y) ident(z) := gen x y; gen z.
Tactic Notation "gen" ident(x) ident(y) ident(z) ident(w) := gen x y z; gen w.

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
