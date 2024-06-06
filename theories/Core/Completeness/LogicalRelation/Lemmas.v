From Coq Require Import Morphisms Morphisms_Relations RelationClasses Relation_Definitions.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import LogicalRelation.Definitions LogicalRelation.Tactics.
Import Domain_Notations.

Add Parametric Morphism M p M' p' : (rel_exp M p M' p')
    with signature (@relation_equivalence domain) ==> iff as rel_exp_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism σ p σ' p' : (rel_sub σ p σ' p')
    with signature (@relation_equivalence env) ==> iff as rel_sub_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Lemma rel_exp_implies_rel_typ : forall {i A p A' p'},
    rel_exp A p A' p' (per_univ i) ->
    exists R, rel_typ i A p A' p' R.
Proof.
  intros.
  destruct_by_head rel_exp.
  destruct_by_head per_univ.
  mauto.
Qed.

#[export]
Hint Resolve rel_exp_implies_rel_typ : mcltt.

Lemma rel_typ_implies_rel_exp : forall {i A p A' p' R},
    rel_typ i A p A' p' R ->
    rel_exp A p A' p' (per_univ i).
Proof.
  intros.
  destruct_by_head rel_typ.
  mauto.
Qed.

#[export]
Hint Resolve rel_typ_implies_rel_exp : mcltt.
