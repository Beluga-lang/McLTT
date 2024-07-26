From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import PER Syntactic.Corollaries.
From Mcltt.Core.Soundness Require Import LogicalRelation.Definitions LogicalRelation.CoreTactics.
From Mcltt.Core.Soundness Require Export Weakening.Lemmas.
Import Domain_Notations.

Lemma pi_glu_exp_pred_pi_glu_typ_pred : forall i IR IP IEl (OP : forall c (equiv_c : {{ Dom c ≈ c ∈ IR }}), glu_typ_pred) elem_rel OEl Γ m M a,
    {{ Γ ⊢ m : M ® a ∈ pi_glu_exp_pred i IR IP IEl elem_rel OEl }} ->
    (forall Δ m' M' b c (equiv_c : {{ Dom c ≈ c ∈ IR }}),
        {{ Δ ⊢ m' : M' ® b ∈ OEl _ equiv_c }} ->
        {{ Δ ⊢ M' ® OP _ equiv_c }}) ->
    {{ Γ ⊢ M ® pi_glu_typ_pred i IR IP IEl OP }}.
Proof.
  inversion_clear 1; econstructor; eauto.
  intros.
  edestruct H5 as [? []]; eauto.
Qed.

Lemma glu_nat_per_nat : forall Γ m a,
    glu_nat Γ m a ->
    {{ Dom a ≈ a ∈ per_nat }}.
Proof.
  induction 1; mauto.
Qed.

#[local]
Hint Resolve glu_nat_per_nat : mcltt.

Lemma glu_nat_escape : forall Γ m a,
    glu_nat Γ m a ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ m : ℕ }}.
Proof.
  induction 1; intros;
    try match goal with
    | H : _ |- _ => solve [gen_presup H; mauto]
    end.
  assert {{ Γ ⊢w Id : Γ }} by mauto.
  match_by_head (per_bot c c) ltac:(fun H => specialize (H (length Γ)) as [L []]).
  clear_dups.
  assert {{ Γ ⊢ m[Id] ≈ L : ℕ }} by mauto.
  gen_presups.
  mauto.
Qed.

#[export]
Hint Resolve glu_nat_escape : mcltt.

Lemma glu_nat_resp_equiv : forall Γ m a,
    glu_nat Γ m a ->
    forall m',
    {{ Γ ⊢ m ≈ m' : ℕ }} ->
    glu_nat Γ m' a.
Proof.
  induction 1; intros; mauto.
  econstructor; trivial.
  intros.
  transitivity {{{ m[σ] }}}; mauto.
Qed.

#[local]
Hint Resolve glu_nat_resp_equiv : mcltt.

Lemma glu_nat_readback : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ b,
      {{ Δ ⊢w σ : Γ }} ->
      {{ Rnf ⇓ ℕ a in length Δ ↘ b }} ->
      {{ Δ ⊢ m [ σ ] ≈ b : ℕ }}.
Proof.
  induction 1; intros; progressive_inversion; gen_presups.
  - transitivity {{{ zero[σ] }}}; mauto.
  - assert {{ Δ ⊢ m'[σ] ≈ M : ℕ }} by mauto.
    transitivity {{{ (succ m')[σ] }}}; mauto 3.
    transitivity {{{ succ m'[σ] }}}; mauto 4.
  - mauto.
Qed.

#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  gen_presups.

Lemma glu_univ_elem_univ_lvl : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ T,
      {{ Γ ⊢ T ® P }} ->
      {{ Γ ⊢ T : Type@i }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; trivial.
Qed.

Lemma glu_univ_elem_typ_resp_equiv : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ T T',
      {{ Γ ⊢ T ® P }} ->
      {{ Γ ⊢ T ≈ T' : Type@i }} ->
      {{ Γ ⊢ T' ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 4.

  split; [trivial |].
  intros.
  assert {{ Δ ⊢ T[σ] ≈ V : Type@i }}; mauto.
Qed.

Lemma glu_univ_elem_trm_resp_typ_equiv : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a T',
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ T ≈ T' : Type@i }} ->
      {{ Γ ⊢ t : T' ® a ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; repeat split; mauto.

  intros.
  assert {{ Δ ⊢ M[σ] ≈ V : Type@i }}; mauto.
Qed.

Lemma glu_univ_elem_typ_resp_ctx_equiv : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ T Δ,
      {{ Γ ⊢ T ® P }} ->
      {{ ⊢ Γ ≈ Δ }} ->
      {{ Δ ⊢ T ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 2;
    econstructor; mauto.
Qed.

Lemma glu_nat_resp_wk' : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ,
      {{ Γ ⊢ m : ℕ }} ->
      {{ Δ ⊢w σ : Γ }} ->
      glu_nat Δ {{{ m[σ] }}} a.
Proof.
  induction 1; intros; gen_presups.
  - econstructor.
    transitivity {{{ zero[σ] }}}; mauto.
  - econstructor; [ |mauto].
    transitivity {{{ (succ m')[σ] }}}; mauto 4.
  - econstructor; trivial.
    intros. gen_presups.
    assert {{ Δ0 ⊢w σ ∘ σ0 : Γ }} by mauto.
    assert {{ Δ0 ⊢ m[σ ∘ σ0] ≈ v : ℕ }} by mauto 4.
    transitivity {{{ m[σ ∘ σ0] }}}; mauto 4.
Qed.

Lemma glu_nat_resp_wk : forall Γ m a,
    glu_nat Γ m a ->
    forall Δ σ,
      {{ Δ ⊢w σ : Γ }} ->
      glu_nat Δ {{{ m[σ] }}} a.
Proof.
  mauto using glu_nat_resp_wk'.
Qed.
#[export]
 Hint Resolve glu_nat_resp_wk : mcltt.

Lemma glu_univ_elem_trm_escape : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a,
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ t : T }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 4.

  match_by_head (per_bot c c) ltac:(fun H => specialize (H (length Γ)) as [Lc []]).
  match_by_head (per_bot b b) ltac:(fun H => specialize (H (length Γ)) as [Lb []]).
  assert {{ Γ ⊢w Id : Γ }} by mauto.
  clear_dups.
  assert {{ Γ ⊢ m[Id] ≈ Lc : M[Id] }} by mauto.
  gen_presups.
  mauto.
Qed.

Lemma glu_univ_elem_per_univ : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Dom A ≈ A ∈ per_univ i }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros; eexists;
    try solve [per_univ_elem_econstructor; try reflexivity; trivial].

  - subst. eapply per_univ_elem_core_univ'; trivial.
    reflexivity.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    mauto.
Qed.

Lemma glu_univ_elem_per_elem : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a R,
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ DF A ≈ A ∈ per_univ_elem i ↘ R }} ->
      {{ Dom a ≈ a ∈ R }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    try do 2 match_by_head1 per_univ_elem invert_per_univ_elem;
    simpl_glu_rel;
    try fold (per_univ j a a);
    mauto 4 using glu_univ_elem_per_univ.

  intros.
  destruct_rel_mod_app.
  destruct_rel_mod_eval.
  functional_eval_rewrite_clear.
  do_per_univ_elem_irrel_assert.

  econstructor; firstorder eauto.
Qed.

Lemma glu_univ_elem_trm_typ : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a,
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ T ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel;
    mauto 4.

  econstructor; eauto.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  intros.
  destruct_rel_mod_eval.
  edestruct H11 as [? []]; eauto.
Qed.

Lemma glu_univ_elem_trm_univ_lvl : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a,
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ T : Type@i }}.
Proof.
  intros. eapply glu_univ_elem_univ_lvl; [| eapply glu_univ_elem_trm_typ]; eassumption.
Qed.

Lemma glu_univ_elem_trm_resp_equiv : forall i P El A,
    {{ DG A ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ t T a t',
      {{ Γ ⊢ t : T ® a ∈ El }} ->
      {{ Γ ⊢ t ≈ t' : T }} ->
      {{ Γ ⊢ t' : T ® a ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel;
    repeat split; mauto 3.

  - repeat eexists; try split; eauto.
    eapply glu_univ_elem_typ_resp_equiv; mauto.

  - econstructor; eauto.
    invert_per_univ_elem H3.
    intros.
    destruct_rel_mod_eval.
    assert {{ Δ ⊢ m' : IT [σ]}} by eauto using glu_univ_elem_trm_escape.
    edestruct H12 as [? []]; eauto.
    eexists; split; eauto.
    enough {{ Δ ⊢ m[σ] m' ≈ t'[σ] m' : OT[σ,,m'] }} by eauto.
    assert {{ Γ ⊢ m ≈ t' : Π IT OT }} as Hty by mauto.
    eassert {{ Δ ⊢ IT[σ] : Type@_ }} by mauto 3.
    eapply wf_exp_eq_sub_cong with (Γ := Δ) in Hty; [| eapply sub_eq_refl; mauto 3].
    autorewrite with mcltt in Hty.
    eapply wf_exp_eq_app_cong with (N := m') (N' := m') in Hty; try pi_univ_level_tac; [|mauto 2].
    autorewrite with mcltt in Hty.
    eassumption.
  - intros.
    assert {{ Δ ⊢ m[σ] ≈ t'[σ] : M[σ] }} by mauto 4.
    mauto 4.
Qed.

Lemma glu_univ_elem_core_univ' : forall j i typ_rel el_rel,
    j < i ->
    (typ_rel <∙> univ_glu_typ_pred j i) ->
    (el_rel <∙> univ_glu_exp_pred j i) ->
    {{ DG 𝕌@j ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel }}.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.
#[export]
Hint Resolve glu_univ_elem_core_univ' : mcltt.

Ltac glu_univ_elem_econstructor :=
  eapply glu_univ_elem_core_univ' + basic_glu_univ_elem_econstructor.

Ltac rewrite_predicate_equivalence_left :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_predicate_equivalence_right :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_predicate_equivalence :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_predicate_equivalence :=
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_right;
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_left;
  clear_predicate_equivalence.

(* Simple Morphism instance for "glu_univ_elem" *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> iff as simple_glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' a.
  split; intro Horig; [gen El' P' | gen El P];
    induction Horig using glu_univ_elem_ind; unshelve glu_univ_elem_econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

(* Morphism instances for "neut_glu_*_pred"s *)
Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> eq ==> eq ==> iff as neut_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition.
Qed.

Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> glu_typ_pred_equivalence as neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_typ_pred_morphism_iff; mauto.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> eq ==> eq ==> eq ==> eq ==> iff as neut_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition;
    match_by_head per_bot ltac:(fun H => rewrite H in *); eassumption.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> glu_exp_pred_equivalence as neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_exp_pred_morphism_iff; mauto.
Qed.

(* Morphism instances for "pi_glu_*_pred"s *)
Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> iff as pi_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> glu_typ_pred_equivalence as pi_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as pi_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> glu_exp_pred_equivalence as pi_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Lemma functional_glu_univ_elem : forall i a P P' El El',
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  simpl.
  intros * Ha Ha'. gen P' El'.
  induction Ha using glu_univ_elem_ind; intros; basic_invert_glu_univ_elem Ha';
    apply_predicate_equivalence; try solve [split; reflexivity].
  assert ((IP <∙> IP0) /\ (IEl <∙> IEl0)) as [] by mauto.
  apply_predicate_equivalence.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => directed invert_per_univ_elem H).
  handle_per_univ_elem_irrel.
  split; [intros Γ C | intros Γ M C m].
  - split; intros []; econstructor; intuition;
      rename a0 into c;
      [rename equiv_a into equiv_c; assert (equiv_c' : in_rel c c) by intuition
      | rename equiv_a into equiv_c'; assert (equiv_c : in_rel0 c c) by intuition];
      destruct_rel_mod_eval;
      rename a0 into b;
      assert ((OP c equiv_c' <∙> OP0 c equiv_c) /\ (OEl c equiv_c' <∙> OEl0 c equiv_c)) as [] by mauto 3;
      intuition.
  - split; intros []; econstructor; intuition;
      clear m;
      rename b into m;
      [rename equiv_b into equiv_m; assert (equiv_m' : in_rel m m) by intuition
      | rename equiv_b into equiv_m'; assert (equiv_m : in_rel0 m m) by intuition];
      destruct_rel_mod_eval;
      [assert (exists am : domain, {{ $| a0 & m |↘ am }} /\ {{ Δ ⊢ m0[σ] m' : OT[σ,,m'] ® am ∈ OEl m equiv_m' }}) by intuition
      | assert (exists am : domain, {{ $| a0 & m |↘ am }} /\ {{ Δ ⊢ m0[σ] m' : OT[σ,,m'] ® am ∈ OEl0 m equiv_m }}) by intuition];
      destruct_conjs;
      assert ((OP m equiv_m' <∙> OP0 m equiv_m) /\ (OEl m equiv_m' <∙> OEl0 m equiv_m)) as [] by mauto 3;
      eexists; split; intuition.
Qed.

Ltac apply_functional_glu_univ_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_univ_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DG ~?A ∈ glu_univ_elem ?i ↘ ?P1 ↘ ?El1 }},
      H2 : {{ DG ~?A ∈ glu_univ_elem ?i' ↘ ?P2 ↘ ?El2 }} |- _ =>
      assert_fails (unify P1 P2; unify El1 El2);
      match goal with
      | H : P1 <∙> P2, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P1 <∙> P2, H0 : El2 <∙> El1 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El2 <∙> El1 |- _ => fail 1
      | _ => assert ((P1 <∙> P2) /\ (El1 <∙> El2)) as [] by (eapply functional_glu_univ_elem; [apply H1 | apply H2]) || tactic_error P1 P2
      end
  end.

Ltac apply_functional_glu_univ_elem :=
  repeat apply_functional_glu_univ_elem1.

Ltac handle_functional_glu_univ_elem :=
  functional_eval_rewrite_clear;
  apply_functional_glu_univ_elem;
  apply_predicate_equivalence;
  clear_dups.

Lemma glu_univ_elem_pi_clean_inversion : forall {i a p B in_rel typ_rel el_rel},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
  {{ DG Π a p B ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel }} ->
  exists elem_rel IP IEl (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred),
    {{ DF Π a p B ≈ Π a p B ∈ per_univ_elem i ↘ elem_rel }} /\
      {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} /\
      (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
          {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
          {{ DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) /\
      (typ_rel <∙> pi_glu_typ_pred i in_rel IP IEl OP) /\
      (el_rel <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hglu.
  basic_invert_glu_univ_elem Hglu.
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  do 5 eexists.
  repeat split.
  1: eassumption.
  1: eassumption.
  1: instantiate (1 := fun c equiv_c Γ M A m => forall (b : domain) Pb Elb,
                        {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ M : A ® m ∈ Elb }}).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ p ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ A ® Pb }}).
  2-5: intros []; econstructor; mauto.
  all: intros.
  - assert {{ Dom c ≈ c ∈ in_rel0 }} as equiv0_c by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c }} by mauto 3.
    apply -> simple_glu_univ_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
  - rename a0 into c.
    rename equiv_a into equiv_c.
    assert {{ Dom c ≈ c ∈ in_rel0 }} as equiv0_c by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    intuition.
  - rename b into c.
    rename equiv_b into equiv_c.
    assert {{ Dom c ≈ c ∈ in_rel0 }} as equiv0_c by intuition.
    assert (exists ac : domain, {{ $| a0 & c |↘ ac }} /\ {{ Δ ⊢ m[σ] m' : OT[σ,,m'] ® ac ∈ OEl c equiv0_c }}) by mauto 3.
    destruct_conjs.
    eexists.
    intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - assert (exists ab : domain,
               {{ $| a0 & b |↘ ab }} /\
                 (forall (b0 : domain) (Pb : glu_typ_pred) (Elb : glu_exp_pred),
                     {{ ⟦ B ⟧ p ↦ b ↘ b0 }} ->
                     {{ DG b0 ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                     {{ Δ ⊢ m[σ] m' : OT[σ,,m'] ® ab ∈ Elb }})) by intuition.
    destruct_conjs.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    eexists.
    intuition.
Qed.

Ltac invert_glu_univ_elem H :=
  (unshelve eapply (glu_univ_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + basic_invert_glu_univ_elem H.

Lemma glu_univ_elem_morphism_helper : forall i a a' P El,
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  simpl.
  intros * [elem_rel Hper] Horig.
  pose proof Hper.
  gen P El.
  induction Hper using per_univ_elem_ind; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Horig; glu_univ_elem_econstructor; try eassumption; mauto;
    handle_per_univ_elem_irrel;
    handle_functional_glu_univ_elem.
  - intros.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    intuition.
  - apply pi_glu_exp_pred_morphism_glu_exp_pred_equivalence; try reflexivity.
  - apply neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
    eassumption.
  - apply neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
    eassumption.
Qed.

(* Morphism instances for "glu_univ_elem" *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ i ==> iff as glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' a a' Haa'.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_morphism_helper; mauto.
  symmetry; eassumption.
Qed.

Add Parametric Morphism i R : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ_elem i R ==> iff as glu_univ_elem_morphism_iff'.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' a a' Haa'.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_morphism_helper; mauto.
  symmetry; mauto.
Qed.

Lemma per_univ_glu_univ_elem : forall i a,
    {{ Dom a ≈ a ∈ per_univ i }} ->
    exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  simpl.
  intros * [? Hper].
  induction Hper using per_univ_elem_ind; intros;
    try solve [do 2 eexists; unshelve (glu_univ_elem_econstructor; try reflexivity; subst; trivial)].

  - destruct_conjs.
    do 2 eexists.
    glu_univ_elem_econstructor; try (eassumption + reflexivity).
    + saturate_refl; eassumption.
    + instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ M A m =>
                          forall b P El,
                            {{ ⟦ B' ⟧ p' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ M : A ® m ∈ El }}).
      instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A =>
                          forall b P El,
                            {{ ⟦ B' ⟧ p' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ A ® P }}).
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      handle_per_univ_elem_irrel.
      rewrite simple_glu_univ_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_univ_elem; intuition.
    + enough {{ DF Π A p B ≈ Π A' p' B' ∈ per_univ_elem i ↘ elem_rel }} by (etransitivity; [symmetry |]; eassumption).
      per_univ_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; mauto.
  - do 2 eexists.
    glu_univ_elem_econstructor; try reflexivity; mauto.
Qed.

#[export]
Instance subrelation_glu_typ_pred_equivalence_iff : subrelation glu_typ_pred_equivalence (@pointwise_relation ctx (predicate (Tcons typ Tnil)) (@pointwise_relation typ (predicate Tnil) iff)).
Proof.
  intros ? ? ? ? ?. intuition.
Qed.

#[export]
Instance subrelation_glu_typ_pred_equivalence_impl : subrelation glu_typ_pred_equivalence (@pointwise_relation ctx (predicate (Tcons typ Tnil)) (@pointwise_relation typ (predicate Tnil) Basics.impl)).
Proof.
  intros ? ? ? ? ? ?. intuition.
Qed.

#[export]
Instance subrelation_glu_exp_pred_equivalence_iff : subrelation glu_exp_pred_equivalence (@pointwise_relation ctx (predicate (Tcons exp (Tcons typ (Tcons domain Tnil)))) (@pointwise_relation exp (predicate (Tcons typ (Tcons domain Tnil))) (@pointwise_relation typ (predicate (Tcons domain Tnil)) (@pointwise_relation domain (predicate Tnil) iff)))).
Proof.
  intros ? ? ? ? ? ? ?. intuition.
Qed.

#[export]
Instance subrelation_glu_exp_pred_equivalence_impl : subrelation glu_exp_pred_equivalence (@pointwise_relation ctx (predicate (Tcons exp (Tcons typ (Tcons domain Tnil)))) (@pointwise_relation exp (predicate (Tcons typ (Tcons domain Tnil))) (@pointwise_relation typ (predicate (Tcons domain Tnil)) (@pointwise_relation domain (predicate Tnil) Basics.impl)))).
Proof.
  intros ? ? ? ? ? ? ? ?. intuition.
Qed.

Typeclasses Transparent Basics.flip.

Lemma ctx_sub_preserves_length : forall {Δ Γ},
    {{ ⊢ Δ ⊆ Γ }} ->
    length Δ = length Γ.
Proof.
  induction 1; simpl; auto.
Qed.

#[export]
Hint Resolve ctx_sub_preserves_length : mcltt.

Lemma weakening_var : forall {Γ σ Δ x A},
    {{ Γ ⊢w σ : Δ }} ->
    {{ #x : A ∈ Δ }} ->
    {{ Γ ⊢ #x[σ] ≈ #(x + length Γ - length Δ) : A[σ] }}.
Proof.
  intros * Hwk. gen A x.
  dependent induction Hwk; intros.
  - gen_presups.
    assert {{ ⊢ Γ ⊆ Δ }} by mauto.
    assert (length Γ = length Δ) by mauto.
    replace (x + length Γ - length Δ) with x by lia.
    assert {{ Γ ⊢ #x[σ] ≈ #x[Id] : A[σ] }} by mauto.
    gen_presups.
    enough {{ Γ ⊢ #x[Id] ≈ #x : A[σ] }}; mauto.
  - assert {{ Δ ⊢ #x : A }} by mauto.
    assert {{ Γ ⊢s τ : Δ, T }} by mauto.
    gen_presups.
    assert {{ Γ ⊢ #x[σ] ≈ #x[Wk∘τ] : A[σ] }} by mauto.
    assert {{ Γ ⊢ A[σ] ≈ A[Wk∘τ] : Type@i }} by mauto.
    assert {{ Δ, T ⊢s Wk : Δ }} by mauto.
    assert {{ Γ ⊢ A[Wk∘τ] ≈ A[Wk][τ] : Type@i }} by mauto.
    assert {{ Γ ⊢ A[σ] ≈ A[Wk][τ] : Type@i }} by mauto.
    assert {{ Γ ⊢ #x[σ] ≈ #x[Wk∘τ] : A[Wk][τ] }} by mauto.
    assert {{ Γ ⊢ #x[Wk∘τ] ≈ #x[Wk][τ] : A[Wk][τ] }} by mauto.
    assert {{ # (S x) : A[Wk] ∈ Δ, T }} by mauto.
    assert {{ Γ ⊢ #(S x)[τ] ≈ #(S x + length Γ - length {{{ Δ, T }}}) : A[Wk][τ] }} by mauto.
    enough {{ Γ ⊢ #x[σ] ≈ #(x + length Γ - length Δ) : A[Wk][τ] }} by mauto 3.
    assert {{ Γ ⊢s τ ≈ τ : Δ, T }} by mauto.
    enough {{ Γ ⊢ #x[Wk][τ] ≈ #(S x)[τ] : A[Wk][τ] }}; mauto 4.
Qed.

Lemma ctx_lookup_implies_length_gt : forall {Γ x A},
    {{ #x : A ∈ Γ }} ->
    length Γ > x.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma glu_univ_elem_exp_var0 : forall {i a P El Γ σ Δ x A},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢w σ : Δ }} ->
    {{ Δ ⊢ A ® P }} ->
    {{ #x : A ∈ Δ }} ->
    {{ Γ ⊢ #x[σ] : A[σ] ® ⇑! a (length Δ - x - 1) ∈ El }}.
Proof.
  simpl in *.
  intros * Hglu. gen A x Γ σ. gen Δ.
  induction Hglu using glu_univ_elem_ind; intros;
    handle_functional_glu_univ_elem.
  - simpl in *.
    assert {{ Γ ⊢s σ : Δ }} by mauto.
    gen_presups.
    assert {{ Δ ⊢ #x : A }} by mauto.
    assert {{ Γ ⊢ A[σ] ≈ Type@j[σ] : Type@i }} by mauto 4.
    assert {{ Γ ⊢ A[σ] ≈ Type@j : Type@i }} by mauto 4.
    repeat split; mauto 3.
    do 2 eexists; split; [econstructor |]; try reflexivity; mauto.
    simpl.
    split; mauto 3.
    intros Δ' σ' **.
    inversion_clear_by_head read_ne.
    assert (length Δ > x) by mauto using ctx_lookup_implies_length_gt.
    replace (length Δ' - (length Δ - x - 1) - 1) with (x + length Δ' - length Δ) by lia.
    assert {{ Δ' ⊢s σ' : Γ }} by mauto.
    assert {{ Δ' ⊢w σ ∘ σ' : Δ }} by mauto.
    assert {{ Δ' ⊢s σ ∘ σ' : Δ }} by mauto.
    assert {{ Δ' ⊢ #x[σ][σ'] ≈ #x[σ∘σ'] : Type@j }} by mauto 4.
    assert {{ Δ' ⊢ A[σ∘σ'] ≈ Type@j[σ∘σ'] : Type@i }} by mauto 4.
    assert {{ Δ' ⊢ A[σ∘σ'] ≈ Type@j : Type@i }} by mauto 4.
    enough {{ Δ' ⊢ #x[σ∘σ'] ≈ #(x + length Δ' - length Δ) : A[σ∘σ'] }} by mauto 4.
    apply weakening_var; mauto.
  - simpl in *.
    assert {{ Γ ⊢s σ : Δ }} by mauto.
    gen_presups.
    assert {{ ⊢ Γ }} by mauto 3.
    assert {{ Γ ⊢ A[σ] ≈ ℕ[σ] : Type@i }} by mauto 4.
    assert (0 <= i) by lia.
    assert {{ Γ ⊢ ℕ[σ] ≈ ℕ : Type@i }} by mauto 4.
    assert {{ Γ ⊢ A[σ] ≈ ℕ : Type@i }} by mauto 4.
    split; mauto 3.
    econstructor; mauto 3.
    intros Δ' σ' **.
    inversion_clear_by_head read_ne.
    assert (length Δ > x) by mauto using ctx_lookup_implies_length_gt.
    replace (length Δ' - (length Δ - x - 1) - 1) with (x + length Δ' - length Δ) by lia.
    assert {{ ⊢ Δ' }} by mauto 3.
    assert {{ Δ' ⊢s σ' : Γ }} by mauto.
    assert {{ Δ' ⊢s σ ∘ σ' : Δ }} by mauto.
    assert {{ Δ' ⊢ #x[σ][σ'] ≈ #x[σ∘σ'] : ℕ }} by mauto 4.
    assert {{ Δ' ⊢ A[σ∘σ'] ≈ ℕ[σ∘σ'] : Type@i }} by mauto 4.
    assert {{ Δ' ⊢ A[σ∘σ'] ≈ ℕ : Type@i }} by mauto 4.
    enough {{ Δ' ⊢ #x[σ∘σ'] ≈ #(x + length Δ' - length Δ) : A[σ∘σ'] }} by mauto 4.
    apply weakening_var; mauto.
  - inversion_clear_by_head pi_glu_typ_pred.
    assert {{ Γ ⊢s σ : Δ }} by mauto.
    gen_presups.
    assert ({{ Δ ⊢ IT : Type@i }} /\ {{ Δ, IT ⊢ OT : Type@i }}) as [] by mauto.
    assert {{ Γ, IT[σ] ⊢s q σ : Δ, IT }} by mauto.
    assert {{ Γ ⊢ A[σ] ≈ Π (IT [σ]) (OT [q σ]) : Type@i }} by mauto 4.
    econstructor; mauto 3.
    + admit. (* by semantic realizability *)
    + intros.
      eapply glu_univ_elem_typ_resp_equiv; mauto.
    + intros Δ' σ' **.
      assert {{ ⊢ Δ' }} by mauto 3.
      assert {{ Δ' ⊢s σ' : Γ }} by mauto.
      assert {{ Δ' ⊢s σ ∘ σ' : Δ }} by mauto.
      assert {{ Δ' ⊢ IT[σ][σ'] ≈ IT[σ∘σ'] : Type@i }} by mauto.
      assert {{ Δ' ⊢ m' : IT[σ∘σ'] ® b ∈ IEl }} by (eapply glu_univ_elem_trm_resp_typ_equiv; mauto).
      assert {{ Δ' ⊢ OT[σ∘σ' ,, m'] ® OP b equiv_b }} by mauto.
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      admit.
  - destruct_by_head neut_glu_typ_pred.
    admit.
    (* econstructor; mauto 3. *)
    (* + assert {{ ⊢ Γ, A }} by mauto 3. *)
    (*   assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3. *)
    (*   econstructor; mauto 3. *)
    (*   intros. *)
    (*   assert {{ Δ ⊢s σ : Γ, A }} as Hσ by mauto. *)
    (*   assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Type@i }} by mauto. *)
    (*   enough {{ Δ ⊢ A[Wk∘σ] ≈ V : Type@i }}; mauto. *)
    (* + intros. *)
    (*   dir_inversion_by_head read_ne; subst. *)
    (*   simpl. *)
    (*   replace (length Δ - length Γ - 1) with (0 + length Δ - length {{{ Γ, A }}}) by (simpl; lia). *)
    (*   assert {{ Δ ⊢s σ : Γ, A }} as Hσ by mauto. *)
    (*   gen_presup Hσ. *)
    (*   apply weakening_var; mauto. *)
Admitted.

Lemma glu_univ_elem_typ_per_univ_escape : forall {i a a' P P' El El' Γ A A'},
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }}.
Proof with mauto 4.
  intros * [elem_rel Hper] Hglu Hglu'.
  gen A' A Γ. gen El' El P' P.
  induction Hper using per_univ_elem_ind; intros; simpl in *;
    saturate_refl_for per_univ_elem;
    handle_per_univ_elem_irrel;
    invert_glu_univ_elem Hglu;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem; mauto 4.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    rename x0 into IP. pose IP.
    rename x1 into IEl. pose IEl.
    assert {{ DG A' ∈ glu_univ_elem i ↘ IP ↘ IEl }} by (match_by_head per_univ_elem ltac:(fun H => rewrite <- H); mauto).
    handle_functional_glu_univ_elem.
    handle_per_univ_elem_irrel.
    destruct_by_head pi_glu_typ_pred.

    assert {{ Γ ⊢ IT ≈ IT0 : Type@i }}.
    {
      assert {{ Γ ⊢ IT[Id] ≈ IT0[Id] : Type@i }} as HIdEq by (eapply IHHper; mauto 4).
      gen_presup HIdEq.
      assert {{ Γ ⊢ IT0[Id] ≈ IT0 : Type@i }} by mauto 4.
      assert {{ Γ ⊢ IT ≈ IT[Id] : Type@i }}...
    }

    assert {{ Γ, IT ⊢ OT ≈ OT0 : Type@i }}.
    {
      assert {{ Dom ⇑! A 0 ≈ ⇑! A 0 ∈ in_rel }} as equiv_0 by admit. (* by semantic realizability *)
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      rename a1 into b.
      rename a2 into b'.
      assert {{ DG b ∈ glu_univ_elem i ↘ x2 d{{{ ⇑! A 0 }}} equiv_0 ↘ x3 d{{{ ⇑! A 0 }}} equiv_0 }} by mauto.
      assert {{ DG b' ∈ glu_univ_elem i ↘ x7 d{{{ ⇑! A 0 }}} equiv_0 ↘ x8 d{{{ ⇑! A 0 }}} equiv_0 }} by mauto.
      assert {{ Γ, IT ⊢w Wk : Γ }} by mauto.
      assert {{ Γ, IT ⊢ OT[Wk,,#0] ® x7 d{{{ ⇑! A 0 }}} equiv_0 }}.
      {
        eapply H12; mauto.
      }
      assert {{ Γ, IT ⊢s Wk,,#0 ≈ Id : Γ, IT }} by admit.
    }

Lemma neut_glu_typ_pred_subtyping : forall {i b b' a a' Γ A},
    {{ Sub ⇑ b a <: ⇑ b' a' at i }} ->
    {{ Γ ⊢ A ® neut_glu_typ_pred i a }} ->
    {{ Γ ⊢ A ® neut_glu_typ_pred i a' }}.
Proof.
  intros * Hsub [].
  inversion_clear Hsub.
  econstructor; mauto 3.
  intros Δ σ V **.
  match_by_head per_bot ltac:(fun H => destruct (H (length Δ)) as [? []]).
  functional_read_rewrite_clear.
  mauto.
Qed.

#[export]
Hint Resolve neut_glu_typ_pred_subtyping : mcltt.

Lemma glu_univ_elem_typ_subtyping_escape : forall {i a a' P P' El El' Γ A A'},
    {{ Sub a <: a' at i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ ⊢ A' ® P' }} ->
    {{ Γ ⊢ A ⊆ A' }}.
Proof with mauto 4.
  intros * Hsub Hglu Hglu'.
  gen A' A Γ. gen El' El P' P.
  induction Hsub; intros; simpl in *;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem; mauto 4.
  - destruct_by_head neut_glu_typ_pred.
    assert (exists L : ne, {{ Rne b in length Γ ↘ L }} /\ {{ Rne b' in length Γ ↘ L }}) as [V []] by mauto.
    assert {{ Γ ⊢ A[Id] ≈ V : Type@i }} by mauto 4.
    assert {{ Γ ⊢ A'[Id] ≈ V : Type@i }} by mauto 4.
    assert {{ Γ ⊢ A ≈ V : Type@i }} by mauto 4.
    enough {{ Γ ⊢ A' ≈ V : Type@i }}...
  - simpl in *.
    gen_presups.
    assert {{ Γ ⊢ Type@i ⊆ Type@j }} by mauto 3.
    enough {{ Γ ⊢ A ⊆ Type@j }}...
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_by_head pi_glu_typ_pred.
    handle_per_univ_elem_irrel.
    match_by_head glu_univ_elem ltac:(fun H' => rewrite H in H').

Lemma glu_univ_elem_typ_subtyping : forall {i a a' P P' El El' Γ A},
    {{ Sub a <: a' at i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    {{ Γ ⊢ A ® P }} ->
    exists A', {{ Γ ⊢ A ⊆ A' }} /\ {{ Γ ⊢ A' ® P' }}.
Proof.
  intros * Hsub Hglu Hglu'.
  gen P P' El El'. gen Γ A.
  induction Hsub; intros; simpl in *;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Hglu;
    invert_glu_univ_elem Hglu';
    handle_functional_glu_univ_elem; eexists.
  - split; mauto 4.
    eapply wf_subtyping_refl.
    destruct_by_head neut_glu_typ_pred.
    eassumption.
  - split; mauto 4.
    simpl in *.
    gen_presups.
    econstructor; mauto 4.
  - simpl in *.
    gen_presups.
    split; [| eapply exp_eq_refl; mauto 3].
    etransitivity; mauto 4.
  - destruct_by_head pi_glu_typ_pred.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    split; mauto 4.
    econstructor; mauto 4; intros.
    + 
    destruct_rel_mod_eval.
    (* Why does "unshelve eapply (per_univ_elem_pi_clean_inversion _) in H2" unshelves "?A'" as well? *)
    Unshelve.
    + unshelve eapply (per_univ_elem_pi_clean_inversion _) in H2; shelve_unifiable; [eassumption |].
      all: (only 1: exact B').
      destruct_conjs.
      idtac.
      destruct H2 as [? []].
      match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
      destruct_by_head pi_glu_typ_pred.
      split.
Admitted.
