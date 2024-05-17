From Coq Require Import Morphisms Morphisms_Relations RelationClasses.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import LogicalRelation.Definitions.
Import Domain_Notations.

Add Parametric Morphism M p M' p' : (rel_exp M p M' p')
    with signature (@relation_equivalence domain) ==> iff as rel_exp_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; eauto;
    apply HRR'; eassumption.
Qed.

Add Parametric Morphism σ p σ' p' : (rel_subst σ p σ' p')
    with signature (@relation_equivalence env) ==> iff as rel_subst_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; eauto;
    apply HRR'; eassumption.
Qed.
