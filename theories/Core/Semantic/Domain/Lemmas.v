From Mcltt.Core Require Import Domain.Definitions.
Import Domain_Notations.

Lemma drop_env_empty_env_no_op :
  d{{{ empty_env ↯ }}} = empty_env.
Proof.
  unfold drop_env; simpl; reflexivity.
Qed.

Lemma drop_env_extend_env_cancel : forall p a,
    d{{{ (p ↦ a) ↯ }}} = p.
Proof.
  unfold drop_env; simpl; reflexivity.
Qed.
