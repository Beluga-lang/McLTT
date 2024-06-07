From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness NbE Presup Soundness System.
From Mcltt.Extraction Require Import NbE.
From Equations Require Import Equations.
Import Domain_Notations.

#[local]
Ltac impl_obl_tac :=
  match goal with
  | |- nbe_order ?G ?M ?A =>
      (on_all_hyp: fun H => apply soundness in H);
      destruct_conjs;
      eapply nbe_order_sound; eassumption
  | |- False =>
      (on_all_hyp: fun H => apply completeness in H);
      destruct_conjs;
      functional_nbe_rewrite_clear;
      congruence
  | _ =>
      (on_all_hyp: fun H => apply soundness in H);
      destruct_conjs;
      functional_nbe_rewrite_clear;
      mauto
  end.

#[tactic="impl_obl_tac"]
Equations conversion_dec G A M (HM : {{ G ⊢ M : A }}) M' (HM' : {{ G ⊢ M' : A }}) : { {{ G ⊢ M ≈ M' : A }} } + { ~ {{ G ⊢ M ≈ M' : A }} } :=
| G, A, M, HM, M', HM' =>
    let (W, HW) := nbe_impl G M A _ in
    let (W', HW') := nbe_impl G M' A _ in
    match nf_eq_dec W W' with
    | left _ => left _
    | right _ => right _
    end.
Next Obligation. impl_obl_tac. Qed.

Equations? typ_subsumption_dec G i A (HA : {{ G ⊢ A : Type@i }}) A' (HA' : {{ G ⊢ A' : Type@i }}) : { {{ G ⊢ A ⊆ A' }} } + { ~ {{ G ⊢ A ⊆ A' }} } :=
| G, i, A, HA, A', HA' =>
    let (W, HW) := nbe_impl G A {{{ Type@i }}} _ in
    let (W', HW') := nbe_impl G A' {{{ Type@i }}} _ in
    match nf_subsumption_dec W W' with
    | left _ => left _
    | right _ => right _
    end.
Proof.
  - impl_obl_tac.
  - impl_obl_tac.
  - (on_all_hyp: fun H => apply soundness in H).
    destruct_conjs.
    functional_nbe_rewrite_clear.
    rename HA into W.
    rename HA' into W'.
    assert {{ G ⊢ W : Type@i }} by (gen_presups; eassumption).
    assert {{ G ⊢ W' : Type@i }} by (gen_presups; eassumption).
    assert {{ G ⊢ W ⊆ W' }} by mauto.
    etransitivity; mauto.
  - admit.
Abort.
  
