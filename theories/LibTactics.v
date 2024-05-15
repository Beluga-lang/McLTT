From Coq Require Export Program.Equality Program.Tactics Lia.

Create HintDb mcltt discriminated.

(** Generalization of Variables *)

Tactic Notation "gen" ident(x) := generalize dependent x.
Tactic Notation "gen" ident(x) ident(y) := gen x; gen y.
Tactic Notation "gen" ident(x) ident(y) ident(z) := gen x y; gen z.
Tactic Notation "gen" ident(x) ident(y) ident(z) ident(w) := gen x y z; gen w.

(** Marking-based Tactics *)

Definition __mark__ (n : nat) A (a : A) : A := a.
Arguments __mark__ n {A} a : simpl never.

Ltac mark H :=
  let t := type of H in
  fold (__mark__ 0 t) in H.
Ltac unmark H := unfold __mark__ in H.

Ltac mark_all :=
  repeat match goal with [H: ?P |- _] =>
    try (match P with __mark__ _ _ => fail 2 end); mark H
  end.
Ltac unmark_all := unfold __mark__ in *.

Ltac on_all_marked_hyp tac :=
  match goal with
  | [ H : __mark__ _ ?A |- _ ] => unmark H; tac H; on_all_marked_hyp tac; try mark H
  | _ => idtac
  end.
Tactic Notation "on_all_marked_hyp:" tactic4(tac) := on_all_marked_hyp tac.
Tactic Notation "on_all_hyp:" tactic4(tac) :=
  mark_all; (on_all_marked_hyp: tac); unmark_all.

Ltac mark_with H n :=
  let t := type of H in
  fold (__mark__ n t) in H.
Ltac mark_all_with n :=
  repeat match goal with [H: ?P |- _] =>
    try (match P with __mark__ _ _ => fail 2 end); mark_with H n
  end.
Ltac unmark_all_with n :=
  repeat match goal with [H: ?P |- _] =>
    match P with __mark__ ?n' _ => tryif unify n n' then unmark H else fail 2 end
  end.

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

Ltac not_let_bind name :=
  match goal with
  | [x := _ |- _] =>
      lazymatch name with
      | x => fail 1
      | _ => fail
      end
  | _ => idtac
  end.

Ltac find_dup_hyp tac non :=
  match goal with
  | [ H : ?X, H' : ?X |- _ ] =>
    not_let_bind H;
    not_let_bind H';
    lazymatch type of X with
    | Prop => tac H H' X
    | _ => idtac
    end
  | _ => non
  end.

Ltac fail_at_if_dup n :=
  find_dup_hyp ltac:(fun H H' X => fail n "dup hypothesis" H "and" H' ":" X)
                      ltac:(idtac).

Ltac fail_if_dup := fail_at_if_dup ltac:(1).

Ltac clear_dups :=
  repeat find_dup_hyp ltac:(fun H H' _ => clear H || clear H')
                             ltac:(idtac).

Ltac clean_replace_by exp0 exp1 tac :=
  tryif unify exp0 exp1
  then fail
  else
    (let H := fresh "H" in
     assert (exp0 = exp1) as H by ltac:(tac);
     subst;
     try rewrite <- H in *).

Tactic Notation "clean" "replace" uconstr(exp0) "with" uconstr(exp1) "by" tactic3(tac) := clean_replace_by exp0 exp1 tac.

Ltac match_by_head1 head tac :=
  match goal with
  | [ H : ?X _ _ _ _ _ _ _ _ _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ _ _ _ _ _ _ _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ _ _ _ _ _ _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ _ _ _ _ _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ _ _ _ _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ _ _ _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ _ _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ _ |- _ ] => unify X head; tac H
  | [ H : ?X _ |- _ ] => unify X head; tac H
  | [ H : ?X |- _ ] => unify X head; tac H
  end.
Ltac match_by_head head tac := repeat (match_by_head1 head ltac:(fun H => tac H; try mark H)); unmark_all.

Ltac inversion_by_head head := match_by_head head ltac:(fun H => inversion H).
Ltac inversion_clear_by_head head := match_by_head head ltac:(fun H => inversion_clear H).
Ltac destruct_by_head head := match_by_head head ltac:(fun H => destruct H).

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

Ltac mautosolve := unshelve solve [mauto]; solve [constructor].


(* Improve type class resolution *)

#[export]
  Hint Extern 1 => eassumption : typeclass_instances.
