From Coq Require Import Lia PeanoNat Relations Program.Equality.
From Mcltt Require Import Axioms Base Domain Evaluate LibTactics PER Readback Syntax System.

Lemma per_univ_elem_sym : forall i A B R,
    per_univ_elem i A B R ->
    exists R', per_univ_elem i B A R' /\ (forall a b, R a b <-> R b a).
Proof.
  intros. induction H using per_univ_elem_ind; subst.
  - exists (per_univ j'). split.
    + apply per_univ_elem_core_univ'; trivial.
    + intros. split; unfold per_univ; intros HD; destruct HD.
      * specialize (H1 _ _ _ H0).
        firstorder.
      * specialize (H1 _ _ _ H0).
        firstorder.
  - admit.
  -


(* Lemma per_univ_univ : forall {i j j'}, *)
(*     j < i -> *)
(*     j = j' -> *)
(*     {{ Dom 𝕌@j ≈ 𝕌@j' ∈ per_univ i }}. *)
(* Proof with solve [mauto]. *)
(*   intros * lt_j_i eq_j_j'. *)
(*   eexists... *)
(*   Unshelve. *)
(*   all: assumption. *)
(* Qed. *)

(* Lemma per_univ_nat : forall {i}, *)
(*     {{ Dom ℕ ≈ ℕ ∈ per_univ i }}. *)
(* Proof with solve [mauto]. *)
(*   intros *. *)
(*   eexists... *)
(* Qed. *)

(* Lemma per_univ_pi_lem : forall {i a a' B p B' p'} *)
(*                            (equiv_a_a' : {{ Dom a ≈ a' ∈ per_univ i }}), *)
(*     (forall {c c'}, *)
(*         {{ Dom c ≈ c' ∈ per_elem equiv_a_a' }} -> *)
(*         rel_mod_eval (per_univ i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}}) -> *)
(*     exists (rel_B_B'_template : forall {c c'}, *)
(*         {{ Dom c ≈ c' ∈ per_elem equiv_a_a' }} -> *)
(*         rel_mod_eval (Per_univ_def.per_univ_template i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}}), *)
(*       (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ per_elem equiv_a_a' }}) *)
(*           b b' (eval_B : {{ ⟦ B ⟧ p ↦ c ↘ b }}) (eval_B' : {{ ⟦ B' ⟧ p' ↦ c' ↘ b' }}), *)
(*           Per_univ_def.per_univ_check i (@per_univ_base i) (rel_mod_eval_equiv (rel_B_B'_template equiv_c_c') eval_B eval_B')). *)
(* Proof with solve [mauto]. *)
(*   intros * rel_B_B'. *)
(*   unshelve epose (rel_B_B'_template := _ : forall {c c'}, *)
(*              {{ Dom c ≈ c' ∈ per_elem equiv_a_a' }} -> *)
(*              rel_mod_eval (Per_univ_def.per_univ_template i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}}). *)
(*   { *)
(*     intros * equiv_c_c'. *)
(*     econstructor; destruct (rel_B_B' _ _ equiv_c_c') as [? ? ?]; only 1-2: solve [mauto]. *)
(*     intros b b' eval_B eval_B'. *)
(*     eapply ex_proj1, rel_mod_eval_equiv... *)
(*   } *)
(*   simpl in rel_B_B'_template. *)
(*   exists rel_B_B'_template. *)
(*   intros *. *)
(*   unfold rel_B_B'_template; simpl. *)
(*   destruct (rel_B_B' _ _ equiv_c_c') as [? ? ?]. *)
(*   eapply ex_proj2. *)
(* Qed. *)

(* Lemma per_univ_pi : forall {i a a' B p B' p'} *)
(*                        (equiv_a_a' : {{ Dom a ≈ a' ∈ per_univ i }}), *)
(*       (forall {c c'}, *)
(*           {{ Dom c ≈ c' ∈ per_elem equiv_a_a' }} -> *)
(*           rel_mod_eval (per_univ i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}}) -> *)
(*       {{ Dom Π a p B ≈ Π a' p' B' ∈ per_univ i }}. *)
(* Proof with solve [mauto]. *)
(*   intros *; destruct equiv_a_a' as [equiv_a_a'_template equiv_a_a'_check]; intro rel_B_B'. *)
(*   eassert (H_per_univ_pi_lem : _). *)
(*   { eapply per_univ_pi_lem... } *)
(*   destruct H_per_univ_pi_lem as [rel_B_B'_template rel_B_B'_check]. *)
(*   eexists; econstructor... *)
(* Qed. *)

(* Lemma per_univ_neut : forall {i m m' a a'}, *)
(*     {{ Dom m ≈ m' ∈ per_bot }} -> *)
(*     {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ per_univ i }}. *)
(* Proof with solve [mauto]. *)
(*   intros * equiv_m_m'. *)
(*   eexists... *)
(*   Unshelve. *)
(*   all: assumption. *)
(* Qed. *)

(* Lemma per_univ_ind : forall i P, *)
(*     (forall j j', j < i -> j = j' -> {{ Dom 𝕌@j ≈ 𝕌@j' ∈ P }}) -> *)
(*     {{ Dom ℕ ≈ ℕ ∈ P }} -> *)
(*     (forall a a' B p B' p' *)
(*         (equiv_a_a' : {{ Dom a ≈ a' ∈ per_univ i }}), *)
(*         {{ Dom a ≈ a' ∈ P }} -> *)
(*         (forall c c', *)
(*             {{ Dom c ≈ c' ∈ per_elem equiv_a_a' }} -> *)
(*             rel_mod_eval (per_univ i) B d{{{ p ↦ c}}} B' d{{{ p' ↦ c'}}}) -> *)
(*         (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ per_elem equiv_a_a' }}), *)
(*             rel_mod_eval P B d{{{ p ↦ c}}} B' d{{{ p' ↦ c'}}}) -> *)
(*         {{ Dom Π a p B ≈ Π a' p' B' ∈ P }}) -> *)
(*     (forall m m' a a', {{ Dom m ≈ m' ∈ per_bot }} -> {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ P }}) -> *)
(*     forall d d', {{ Dom d ≈ d' ∈ per_univ i }} -> {{ Dom d ≈ d' ∈ P }}. *)
(* Proof with solve [mauto]. *)
(*   intros * Huniv Hnat Hpi Hneut d d' [equiv_d_d'_template equiv_d_d'_check]. *)
(*   induction equiv_d_d'_check; only 1-2,4: solve [mauto]. *)
(*   unshelve epose (equiv_a_a'_real := _ : {{ Dom a ≈ a' ∈ per_univ i }}). *)
(*   { econstructor... } *)
(*   eapply Hpi with (equiv_a_a' := equiv_a_a'_real); subst equiv_a_a'_real; [solve [mauto]| |]; *)
(*     intros * equiv_c_c'; unfold per_elem, Per_univ_def.per_elem in equiv_c_c'; destruct (rel_B_B' _ _ equiv_c_c'). *)
(*   - econstructor; only 1-2: solve [mauto]. *)
(*     intros b b' eval_B eval_B'. *)
(*     econstructor; apply H. *)
(*     Unshelve. *)
(*     3-5: eassumption. *)
(*   - econstructor; only 1-2: solve [mauto]. *)
(*     intros b b' eval_B eval_B'. *)
(*     eapply H0; solve [mauto]. *)
(* Qed. *)

Lemma per_univ_sym : forall m m' i,
    {{ Dom m ≈ m' ∈ per_univ i }} ->
    {{ Dom m' ≈ m ∈ per_univ i }}
with per_elem_sym : forall m m' i R R'
  (equiv_m_m' : {{ DF m ≈ m' ∈ per_univ_elem i ↘ R }})
  (equiv_m'_m : {{ DF m' ≈ m ∈ per_univ_elem i ↘ R' }}),
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Dom m' ≈ m ∈ R' }}.
Proof with mauto.
  - intros.
    destruct H as [per_elem Hper_univ].
    unfold in_dom_fun_rel in *.
    dependent induction Hper_univ; try solve [subst; eexists; econstructor; mauto].
    + fold per_univ_elem in equiv_a_a'.
    (*   eexists; econstructor... *)
    (* +  *)
    (* unfold per_univ, Per_univ_def.per_univ, in_dom_rel in *. *)
    (* destruct H as [equiv_a_a' Hcheck]. *)
    (* dependent induction Hcheck; subst. *)
    (* + eexists. *)
    (*   eapply Per_univ_def.per_univ_check_univ. *)
    (*   Unshelve. all: auto. *)
    (* + eexists. *)
    (*   econstructor. *)
    (* + destruct IHHcheck. *)
    (*   assert (Per_univ_def.per_univ_template i d{{{ Π a' p' B'}}} d{{{ Π a p B}}}). *)
    (*   { eapply (@Per_univ_def.per_univ_template_pi i _ _ _ _ _ _ (per_univ i) (fun _ _ => per_elem) (ex_intro _ x H1)). *)
    (*     intros. *)
    (*     unfold in_dom_rel, per_elem, Per_univ_def.per_elem in *. *)
    (*   } *)
    (*   eexists. *)
    (*   econstructor. *)
    (*   * eassumption. *)
    (*   * intros. *)
      
