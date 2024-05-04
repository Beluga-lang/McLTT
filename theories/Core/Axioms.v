Require Export Coq.Logic.FunctionalExtensionality.

Lemma exists_absorption :
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (exists x : A, P x) /\ Q <-> (exists x : A, P x /\ Q).
Proof.
  firstorder.
Qed.
