From Coq Require Import Lia PeanoNat Relation_Definitions.
From Equations Require Import Equations.
From Mcltt Require Import Base Domain Evaluate EvaluateLemmas LibTactics PER PERLemmas Syntax System.

Lemma per_nat_then_per_top : forall {n m},
    {{ Dom n ≈ m ∈ per_nat }} ->
    {{ Dom ⇓ ℕ n ≈ ⇓ ℕ m ∈ per_top }}.
Proof.
  induction 1; simpl in *; intros.
  - eexists; firstorder econstructor.
  - specialize (IHper_nat s) as [? []].
    eexists; firstorder (econstructor; eauto).
  - specialize (H s) as [? []].
    eexists; firstorder (econstructor; eauto).
Qed.

#[export]
Hint Resolve per_nat_then_per_top : mcltt.

Section Per_univ_elem_realize.
  Variable (i : nat) (rec_per_univ_then_per_top_typ : forall j, j < i -> forall a a' R, {{ DF a ≈ a' ∈ per_univ_elem j ↘ R }} -> {{ Dom a ≈ a' ∈ per_top_typ }}).

  Lemma realize_per_univ_elem_gen : forall a a' R,
      {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
      {{ Dom a ≈ a' ∈ per_top_typ }}
      /\ (forall {c c'}, {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }})
      /\ (forall {b b'}, {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}).
  Proof with (solve [(((eexists; split) || idtac; econstructor) || idtac); mauto]) using i rec_per_univ_then_per_top_typ.
    intros * H; simpl in H.
    induction H using per_univ_elem_ind; repeat split; intros.
    - subst; intro s...
    - eexists.
      per_univ_elem_econstructor.
      eauto.
    - intro s.
      firstorder.
      assert {{ Dom b ≈ b' ∈ per_top_typ }} as top_typ_b_b' by (eapply rec_per_univ_then_per_top_typ; eassumption).
      specialize (top_typ_b_b' s); destruct_all...
    - intro s...
    - idtac...
    - eauto using per_nat_then_per_top.
    - specialize (IHper_univ_elem rec_per_univ_then_per_top_typ) as [? []].
      intro s.
      assert {{ Dom ⇑! A s ≈ ⇑! A' s ∈ in_rel }} by eauto using var_per_bot.
      destruct_rel_mod_eval.
      specialize (H10 rec_per_univ_then_per_top_typ) as [? []].
      specialize (H10 (S s)) as [? []].
      specialize (H3 s) as [? []]...
    - rewrite H2; clear H2.
      intros c0 c0' equiv_c0_c0'.
      specialize (IHper_univ_elem rec_per_univ_then_per_top_typ) as [? []].
      destruct_rel_mod_eval.
      specialize (H9 rec_per_univ_then_per_top_typ) as [? []].
      econstructor; try solve [econstructor; eauto].
      enough ({{ Dom c ⇓ A c0 ≈ c' ⇓ A' c0' ∈ per_bot }}) by mauto.
      intro s.
      specialize (H3 s) as [? [? ?]].
      specialize (H5 _ _ equiv_c0_c0' s) as [? [? ?]]...
    - rewrite H2 in *; clear H2.
      specialize (IHper_univ_elem rec_per_univ_then_per_top_typ) as [? []].
      intro s.
      assert {{ Dom ⇑! A s ≈ ⇑! A' s ∈ in_rel }} by eauto using var_per_bot.
      destruct_rel_mod_eval.
      specialize (H10 rec_per_univ_then_per_top_typ) as [? []].
      destruct_rel_mod_app.
      assert {{ Dom ⇓ a fa ≈ ⇓ a' f'a' ∈ per_top }} by mauto.
      specialize (H2 s) as [? []].
      specialize (H16 (S s)) as [? []]...
    - intro s.
      specialize (H s) as [? []]...
    - idtac...
    - intro s.
      specialize (H s) as [? []].
      inversion_clear H0.
      specialize (H2 s) as [? []]...
  Qed.
End Per_univ_elem_realize.

Equations per_univ_then_per_top_typ (i : nat) : forall a a' R, {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} -> {{ Dom a ≈ a' ∈ per_top_typ }} by wf i :=
| i => fun _ _ _ H => proj1 (realize_per_univ_elem_gen i (fun {j} lt_j_i => per_univ_then_per_top_typ j) _ _ _ H).
Arguments per_univ_then_per_top_typ {_ _ _ _}.

#[export]
Hint Resolve per_univ_then_per_top_typ : mcltt.

Lemma per_bot_then_per_elem : forall {i a a' R c c'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }}.
Proof.
  intros.
  eapply realize_per_univ_elem_gen; mauto.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)

Lemma per_elem_then_per_top : forall {i a a' R b b'},
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}.
Proof.
  intros.
  eapply realize_per_univ_elem_gen; mauto.
Qed.

#[export]
Hint Resolve per_elem_then_per_top : mcltt.
