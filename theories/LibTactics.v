From Coq Require Export Program.Equality Program.Tactics Lia RelationClasses.

Open Scope predicate_scope.

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

Ltac mark_with H n :=
  let t := type of H in
  fold (__mark__ n t) in H.
Ltac mark_all_with n :=
  repeat match goal with [H: ?P |- _] =>
    try (match P with __mark__ _ _ => fail 2 end); mark_with H n
  end.
Ltac unmark_all_with n :=
  repeat match goal with [H: ?P |- _] =>
    match P with __mark__ ?n' _ => tryif unify n n' then unmark H else fail 1 end
  end.

Ltac on_all_marked_hyp tac :=
  repeat match goal with
    | [ H : __mark__ _ ?A |- _ ] => unmark H; tac H
    end.
Ltac on_all_marked_hyp_rev tac :=
  repeat match reverse goal with
    | [ H : __mark__ _ ?A |- _ ] => unmark H; tac H
    end.
Tactic Notation "on_all_marked_hyp:" tactic4(tac) := on_all_marked_hyp tac; unmark_all_with 0.
Tactic Notation "on_all_marked_hyp_rev:" tactic4(tac) := on_all_marked_hyp_rev tac; unmark_all_with 0.
Tactic Notation "on_all_hyp:" tactic4(tac) :=
  mark_all_with 0; (on_all_marked_hyp: tac).
Tactic Notation "on_all_hyp_rev:" tactic4(tac) :=
  mark_all_with 0; (on_all_marked_hyp_rev: tac).

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
    | _ => fail
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

Ltac directed tac :=
  let ng := numgoals in
  tac;
  let ng' := numgoals in
  guard ng' <= ng.

Tactic Notation "directed" tactic2(tac) := directed tac.

Ltac progressive_invert H :=
  (* dependent destruction is more general than inversion *)
  directed dependent destruction H.

#[local]
  Ltac progressive_invert_once H n :=
  let T := type of H in
  lazymatch T with
  | __mark__ _ _ => fail
  | forall _, _ => fail
  | _ => idtac
  end;
  lazymatch type of T with
  | Prop => idtac
  | Type => idtac
  end;
  directed inversion H;
  simplify_eqs;
  clear_refl_eqs;
  clear_dups;
  try mark_with H n.

#[global]
  Ltac progressive_inversion :=
  clear_dups;
  repeat match goal with
    | H : _ |- _ =>
        progressive_invert_once H 100
    end;
  unmark_all_with 100.

Ltac clean_replace_by exp0 exp1 tac :=
  tryif unify exp0 exp1
  then fail
  else
    (let H := fresh "H" in
     assert (exp0 = exp1) as H by ltac:(tac);
     subst;
     try rewrite <- H in *).

Tactic Notation "clean" "replace" uconstr(exp0) "with" uconstr(exp1) "by" tactic3(tac) := clean_replace_by exp0 exp1 tac.

#[global]
  Ltac find_head t :=
  lazymatch t with
  | ?t' _ => find_head t'
  | _ => t
  end.

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
Ltac dir_inversion_by_head head := match_by_head head ltac:(fun H => directed inversion H).
Ltac inversion_clear_by_head head := match_by_head head ltac:(fun H => inversion_clear H).
Ltac dir_inversion_clear_by_head head := match_by_head head ltac:(fun H => directed inversion_clear H).
Ltac destruct_by_head head := match_by_head head ltac:(fun H => destruct H).
Ltac dir_destruct_by_head head := match_by_head head ltac:(fun H => directed destruct H).

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

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) :=
  eauto pow using use1, use2, use3 with mcltt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) "," uconstr(use4) :=
  eauto pow using use1, use2, use3, use4 with mcltt core.

Ltac mautosolve_impl pow := unshelve solve [mauto pow]; solve [constructor].

Tactic Notation "mautosolve" := mautosolve_impl integer:(5).
Tactic Notation "mautosolve" int_or_var(pow) := mautosolve_impl pow.

(* Improve type class resolution *)

#[export]
  Hint Extern 1 => eassumption : typeclass_instances.

Ltac predicate_resolve :=
  lazymatch goal with
  | |- @Reflexive _ (@predicate_equivalence _) =>
      simple apply @Equivalence_Reflexive
  | |- @Symmetric _ (@predicate_equivalence _) =>
      simple apply @Equivalence_Symmetric
  | |- @Transitive _ (@predicate_equivalence _) =>
      simple apply @Equivalence_Transitive
  end.

#[export]
 Hint Extern 1 => predicate_resolve : typeclass_instances.


(* intuition tactic default setting *)
Ltac Tauto.intuition_solver ::= auto with mcltt core solve_subterm.

Ltac exvar T tac :=
  lazymatch type of T with
  | Prop =>
      let H := fresh "H" in
      unshelve evar (H : T);
      [|
        let H' := eval unfold H in H in
          clear H; tac H']
  | _ =>
      let x := fresh "x" in
      evar (x : T);
      let x' := eval unfold x in x in
        clear x; tac x'
  end.

(* this tactic traverses to the bottom of a lemma following universals and conjunctions to the bottom and apply a tactic *)
Ltac deepexec lem tac :=
  let T := type of lem in
  let T' := eval simpl in T in
  let ST := eval unfold iff in T' in
  match ST with
  | _ /\ _ => deepexec constr:(proj1 lem) tac
            || deepexec constr:(proj2 lem) tac
  | forall _ : ?T, _ =>
      exvar T ltac:(fun x =>
                      lazymatch type of T with
                      | Prop => match goal with
                            | H : _ |- _ => unify x H
                            | _ => idtac
                            end
                      | _ => idtac
                      end;
                      deepexec constr:(lem x) tac)
  | _ => tac lem
  end.

(* this tactic is similar to above, but the traversal cuts off when it sees an assumption applicable to a cut-off argument C *)
Ltac cutexec lem C tac :=
  let CT := type of C in
  let T := type of lem in
  let T' := eval simpl in T in
  let ST := eval unfold iff in T' in
  lazymatch ST with
  | _ /\ _ => cutexec constr:(proj1 lem) C tac
            || cutexec constr:(proj2 lem) C tac
  | forall _ : ?T, _ =>
      exvar T ltac:(fun x =>
                      tryif unify T CT
                      then
                        unify x C;
                        tac lem
                      else
                        (lazymatch type of T with
                         | Prop => match goal with
                               | H : _ |- _ => unify x H
                               | _ => idtac
                               end
                         | _ => idtac
                         end;
                         cutexec constr:(lem x) C tac))
  | _ => tac lem
  end.


Ltac unify_args H P :=
  lazymatch P with
  | ?P' ?x =>
      let r := unify_args H P' in
      constr:(r x)
  | _ => H
  end.

#[global]
  Ltac strong_apply H X :=
  let H' := fresh "H" in
  let T := type of X in
  let R := unify_args H T in
  cutexec R X ltac:(fun L => pose proof (L X) as H'; simpl in H'; clear X; rename H' into X).


#[global]
  Ltac apply_equiv_left1 :=
  let tac1 := fun H R H1 T => (let h := find_head T in unify R h; strong_apply H H1) in
  let tac2 := fun H R G => (let h := find_head G in unify R h; apply H; simpl) in
  match goal with
  | H : ?R <∙> _, H1 : ?T |- _ => progress tac1 H R H1 T
  | H : relation_equivalence ?R _, H1 : ?T |- _ => progress tac1 H R H1 T
  | H : ?R <∙> _ |- ?G => progress tac2 H R G
  | H : relation_equivalence ?R _ |- ?G => progress tac2 H R G
  end.


#[global]
  Ltac apply_equiv_left := repeat apply_equiv_left1.


#[global]
  Ltac apply_equiv_right1 :=
  let tac1 := fun H R H1 T => (let h := find_head T in unify R h; strong_apply H H1) in
  let tac2 := fun H R G => (let h := find_head G in unify R h; apply H; simpl) in
  match goal with
  | H : _ <∙> ?R, H1 : ?T |- _ => progress tac1 H R H1 T
  | H : relation_equivalence _ ?R, H1 : ?T |- _ => progress tac1 H R H1 T
  | H : _ <∙> ?R |- ?G => progress tac2 H R G
  | H : relation_equivalence _ ?R |- ?G => progress tac2 H R G
  end.

#[global]
  Ltac apply_equiv_right := repeat apply_equiv_right1.
