From Coq Require Import Relations RelationClasses.
From Mcltt Require Import Base LibTactics LogicalRelation System.
Import Domain_Notations.

Lemma rel_exp_pi_cong : forall {i Γ A A' B B'},
  {{ Γ ⊨ A ≈ A' : Type@i }} ->
  {{ Γ , A ⊨ B ≈ B' : Type@i }} ->
  {{ Γ ⊨ Π A B ≈ Π A' B' : Type@i }}.
Proof.
  intros * [env_relΓ] [env_relΓA].
  destruct_conjs.
  match_by_head1 per_ctx_env ltac:(fun H => inversion H; let n := numgoals in guard n <= 1); subst.
  per_ctx_env_irrel_rewrite.
  eexists.
  eexists; [eassumption |].
  eexists.
  intros.
  (on_all_hyp: fun H => destruct_rel_by_assumption env_relΓ H).
  destruct_by_head rel_typ.
  inversion_by_head (eval_exp {{{ Type@i }}}); subst.
  destruct_by_head rel_exp.
  invert_per_univ_elem H12.
  clear_refl_eqs.
  destruct_conjs.
  per_univ_elem_irrel_rewrite.
  exists (per_univ i).
  split; [> econstructor; only 1-2: repeat econstructor; eauto ..].
  exists (* There's no way to give the correct R here!!!! *)
  (* per_univ_elem_econstructor. try now eauto. *)
  (* - econstructor; unfold Symmetric, Transitive; intros; [eapply per_elem_sym | eapply per_elem_trans]; mauto. *)
  (* - intros. *)
  (*   specialize (H2 d{{{ p ↦ c }}} d{{{ p' ↦ c' }}} (ex_intro _ equiv_p_p' equiv_c_c')). *)
  (*   destruct_conjs. *)
  (*   destruct_by_head rel_typ. *)
  (*   inversion_by_head (eval_exp {{{ Type@i }}}); subst. *)
  (*   destruct_by_head rel_exp. *)
  (*   per_univ_elem_irrel_rewrite. *)
  (*   destruct_conjs. *)
  (*   econstructor; eauto. *)
  (*   eapply H2. *)
    
