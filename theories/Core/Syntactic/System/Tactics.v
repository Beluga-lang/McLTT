From Mcltt Require Import Base LibTactics.
From Mcltt Require Export System.Definitions.
Import Syntax_Notations.

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
