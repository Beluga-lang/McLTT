From Coq Require Import Lia PeanoNat Relations Program.Equality.
From Mcltt Require Import Axioms Base Domain Evaluate LibTactics PER Readback Syntax System.
From Equations Require Import Equations.
From Coq.Logic Require Import ChoiceFacts.


Lemma per_univ_elem_right_irrel_gen : forall i A B R,
    per_univ_elem i A B R ->
    forall A' B' R',
      A = A' ->
      per_univ_elem i A' B' R' ->
      R = R'.
Proof.
  induction 1 using per_univ_elem_ind; intros ? ? ? Heq Hright;
    try solve [induction Hright using per_univ_elem_ind;
               try congruence].

  subst.
  simp per_univ_elem in Hright; inversion Hright; try congruence; subst.
  rewrite <- per_univ_elem_equation_1 in *.
  unfold in_dom_fun_rel in *.
  specialize (IHper_univ_elem _ _ _ eq_refl equiv_a_a').
  subst.
  extensionality f.
  extensionality f'.
  rewrite H0, H7.
  extensionality c.
  extensionality c'.
  extensionality equiv_c_c'.
  specialize (H1 _ _ equiv_c_c').
  destruct H1 as [? [[? ? ? ? [? ?]] ?]].

  specialize (H8 _ _ equiv_c_c').
  destruct H8 as [? [[? ? ? ? ?] ?]].

  assert (a = a0) by admit.
  subst.
  specialize (H4 _ _ _ eq_refl H9).
  subst.
  congruence.
Admitted.

Lemma per_univ_elem_right_irrel : forall i A B R B' R',
    per_univ_elem i A B R ->
    per_univ_elem i A B' R' ->
    R = R'.
Proof.
  intros. eauto using per_univ_elem_right_irrel_gen.
Qed.

Lemma per_univ_elem_sym : forall i A B R,
    per_univ_elem i A B R ->
    exists R', per_univ_elem i B A R' /\ (forall a b, R a b <-> R' b a).
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
  - destruct IHper_univ_elem as [in_rel' [? ?]].
    unfold in_dom_rel in *.
    setoid_rewrite rel_mod_eval_simp_ex in H1.
    setoid_rewrite exists_absorption in H1.
    repeat setoid_rewrite dep_functional_choice_equiv in H1.
    destruct H1 as [out_rel [out_rel' ?]].
    assert (forall a b : domain, in_rel' a b -> in_rel b a) as Hconv by firstorder.
    setoid_rewrite H0.
    exists (fun f f' => forall (c c' : domain) (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel' }}), rel_mod_app (out_rel' c' c (Hconv _ _ equiv_c_c')) f' c' f c).
    split.
    + simp per_univ_elem; econstructor; try rewrite <- per_univ_elem_equation_1 in *; eauto.
      * intros. reflexivity.
      * intros.
        destruct (H1 _ _ (Hconv _ _ equiv_c_c')) as [[? ? ? ? [? [? ?]]] ?].
        exists (out_rel c' c (Hconv c c' equiv_c_c')). split; try econstructor; eauto.
        admit.

        intros.
        apply propositional_extensionality.
        split; intros HR; destruct HR; econstructor; eauto; firstorder.

    + split; intros.
      * destruct (H1 _ _ (Hconv _ _ equiv_c_c')) as [[? ? ? ? [? [? ?]]] ?].
        specialize (H4 _ _ (Hconv c c' equiv_c_c')).
        rewrite H10 in H4.
        destruct H4; econstructor; eauto; firstorder.

        unfold in_dom_rel in *. rewrite <- H9. firstorder.

(* Lemma per_univ_elem_sym : forall i A B R, *)
(*     per_univ_elem i A B R -> *)
(*     per_univ_elem i B A R. *)
(* Proof. *)
(*   intros. induction H using per_univ_elem_ind; subst. *)
(*   - apply per_univ_elem_core_univ'; trivial. *)
(*   - admit. *)
(*   - simp per_univ_elem; econstructor; try rewrite <- per_univ_elem_equation_1 in *; eauto. *)
(*     intros. *)
(*     destruct (H1 _ _ equiv_c_c') as [? [[? ? ? ? [? ?]] ?]]. *)
(*     eexists. split; try eassumption. *)
(*     econstructor; eauto. *)

(*     specialize (H1 _ _ equiv_c_c'). *)
(*     destruct H1 as *)


Lemma per_univ_elem_sym : forall i A B R,
    per_univ_elem i A B R ->
    per_univ_elem i B A R /\ (forall a b, R a b <-> R b a).
Proof.
  intros. induction H using per_univ_elem_ind; subst.
  - split.
    + apply per_univ_elem_core_univ'; trivial.
    + intros. split; unfold per_univ; intros HD; destruct HD.
      * specialize (H1 _ _ _ H0).
        firstorder.
      * specialize (H1 _ _ _ H0).
        firstorder.
  - admit.
  - destruct IHper_univ_elem as [? ?].

    unfold in_dom_rel in *.
    split.
    + simp per_univ_elem; econstructor; try rewrite <- per_univ_elem_equation_1 in *; eauto.
      intros.
      destruct (H1 _ _ equiv_c_c') as [? [[? ? ? ? [? [? ?]]] ?]].
      assert (in_rel c' c) by firstorder.
      destruct (H1 _ _ H10) as [? [[? ? ? ? [? [? ?]]] ?]].
      eexists. split; try eassumption.
      econstructor; eauto.
      eexists.

      admit.
    + assert (forall a b, elem_rel a b -> elem_rel b a). {
        intros.
        rewrite H0 in *.
        intros.
        destruct (H1 _ _ equiv_c_c') as [? [[? ? ? ? [? [? ?]]] ?]].
        rewrite H10.

        (* econstructor. *)

        assert (in_rel c' c) by firstorder.
        (* destruct (H1 _ _ H11) as [? [[? ? ? ? [? [? ?]]] ?]]. *)
        assert (rel_mod_app x0 a c' b c) by admit.
        destruct H18.
        rewrite H17 in H4.
      }
      firstorder.


      intros.
      do 2 rewrite H0.

      extensionality c.
      extensionality c'.
      extensionality equiv_c_c'.

    setoid_rewrite H3 in H1.
    setoid_rewrite rel_mod_eval_simp_ex in H0.
    setoid_rewrite exists_absorption in H0.
    repeat setoid_rewrite dep_functional_choice_equiv in H0.
    destruct H0 as [out_rel [out_rel' ?]].
    setoid_rewrite <- and_assoc in H0.

    setoid_rewrite rel_mod_eval_simp_and in H0.

    repeat setoid_rewrite functional_choice_equiv in H0.
    setoid_rewrite and_comm in H0.
    setoid_rewrite exists_absorption in H0.

    assert (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
             exists R', rel_mod_eval (fun (x y : domain) (z : relation domain) =>
                                   per_univ_elem i x y z /\
                                     (per_univ_elem i y x R' /\ (forall a b : domain, z a b <-> R' b a)))
                     B d{{{p ↦ c}}} B' d{{{ p' ↦ c'}}} (out_rel c c' equiv_c_c')).
    {
      intros. specialize (H0 _ _ equiv_c_c').
      destruct H0.
      unfold in_dom_fun_rel in H5.
      destruct H5 as [? [R' [? ?]]].
      exists R'. econstructor; unfold in_dom_fun_rel; eauto.
    }
    unfold in_dom_rel in *.
    setoid_rewrite H3 in H4.

    clear H0
    repeat setoid_rewrite dep_functional_choice_equiv in H4.
    destruct H4 as [out_rel' ?].
    exists (fun f' f => forall c' c (equiv_c'_c : R c' c), rel_mod_app (out_rel' _ _ ()) f' c' f c).

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
    {{ Dom m ≈ m' ∈ per_univ i }} -> {{ Dom m' ≈ m ∈ per_univ i }}
with per_elem_sym : forall m m' i R R' a a'
  (equiv_m_m' : {{ DF m ≈ m' ∈ per_univ_elem i ↘ R }})
  (equiv_m'_m : {{ DF m' ≈ m ∈ per_univ_elem i ↘ R' }}),
    {{ Dom a ≈ a' ∈ R }} <-> {{ Dom a' ≈ a ∈ R' }}.
Proof with mauto.
  all: intros *; try split.
  1: intro Hper_univ.
  2-3: intro Hper_elem.
  - destruct Hper_univ as [per_elem equiv_m_m'].
    autorewrite with per_univ_elem in equiv_m_m'.
    dependent induction equiv_m_m'; subst; only 1-2,4: solve [eexists; econstructor; mauto].
    (* Pi case *)
    destruct IHequiv_m_m' as [in_rel' IHequiv_a_a'].
    rewrite <- per_univ_elem_equation_1 in H, equiv_a_a'.
    (* (* One attempt *) *)
    (* unshelve epose (out_rel' := _ : forall c' c : domain, {{ Dom c' ≈ c ∈ in_rel' }} -> relation domain). *)
    (* { *)
    (*   intros * equiv_c'_c. *)
    (*   assert (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}) by (erewrite per_elem_sym; eassumption). *)
    (*   assert (rel_mod_eval (per_univ_elem i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel c c' equiv_c_c')) by mauto. *)
    (*   (* Failure point *) *)
    (*   destruct_last. *)
    (* } *)

    (* (* The other *) *)
    (* assert (exists (out_rel' : forall c' c : domain, {{ Dom c' ≈ c ∈ in_rel' }} -> relation domain), *)
    (*          forall (c' c : domain) (equiv_c'_c : {{ Dom c' ≈ c ∈ in_rel' }}), *)
    (*            rel_mod_eval (per_univ_elem i) B' d{{{ p' ↦ c' }}} B d{{{ p ↦ c }}} (out_rel' c' c equiv_c'_c)). *)
    (* { *)
    (*   (* This "eexists" is problematic *) *)
    (*   eexists. *)
    (*   intros. *)
    (*   assert (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}) by (erewrite per_elem_sym; eassumption). *)
    (*   assert (rel_mod_eval (per_univ_elem i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel c c' equiv_c_c')) by mauto. *)
    (*   destruct_last. *)
    (*   econstructor; try eassumption. *)
    (* } *)
      
