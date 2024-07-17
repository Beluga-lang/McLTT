From Mcltt Require Import Base LibTactics.
From Mcltt Require Export System.Definitions System.Lemmas.
Import Syntax_Notations.

#[global]
Ltac pi_univ_level_tac :=
  match goal with
  | |- {{ ~_ ⊢s ~_ : ~_ }} => mauto 4
  | H : {{ ~?Δ ⊢ ~?A : Type@?j }} |- {{ ~?Δ , ~?A ⊢ ~?B : Type@?i }} =>
      eapply lift_exp_max_right; mauto 4
  | |- {{ ~?Δ ⊢ ~?A : Type@?j }} =>
      eapply lift_exp_max_left; mauto 4
  end.

#[export]
Hint Rewrite -> wf_exp_eq_pi_sub using pi_univ_level_tac : mcltt.

#[local]
Ltac invert_wf_ctx1 H :=
  match type of H with
  | {{ ⊢ ~_ , ~_ }} =>
      let H' := fresh "H" in
      pose proof H as H';
      progressive_invert H'
  end.

Ltac invert_wf_ctx :=
  (on_all_hyp: fun H => invert_wf_ctx1 H);
  clear_dups.
