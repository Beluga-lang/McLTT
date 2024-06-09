From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness NbE Soundness SystemOpt.
From Mcltt.Extraction Require Import NbE.
From Equations Require Import Equations.
Import Domain_Notations.

Section nf_subsumption_dec.
  #[local]
  Ltac impl_obl_tac :=
    match goal with
    | |- nf_subsumption _ _ => mauto 2
    | A := _ : nf |- ~ (nf_subsumption _ _) =>
        let H := fresh "H" in
        subst A; intro H; dependent destruction H; congruence
    | |- ~ (nf_subsumption _ _) =>
        let H := fresh "H" in
        intro H; dependent destruction H; lia
    end.

  #[tactic=impl_obl_tac]
  Equations nf_subsumption_dec A A' : {nf_subsumption A A'} + {~ nf_subsumption A A'} :=
  | n{{{ Type@i }}}, n{{{ Type@j }}} =>
      match Compare_dec.le_lt_dec i j with
      | left _ => left _
      | right _ => right _
      end
  (* Here we have a separate clause for n{{{ Type@i }}} so that we can extract a more efficient code *)
  | n{{{ Type@i }}}, _ => right _
  | A, A' =>
      match nf_eq_dec A A' with
      | left _ => left _
      | right _ => right _
      end.
End nf_subsumption_dec.

Section conversion_dec.
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
End conversion_dec.

Section typ_subsumption_dec.
  #[local]
  Ltac impl_obl_tac :=
    match goal with
    | |- nbe_order ?G ?M ?A =>
        (on_all_hyp: fun H => apply soundness in H);
        destruct_conjs;
        eapply nbe_order_sound; eassumption
    | H: nbe ?G ?A {{{ Type@?i }}} ?W, H': nbe ?G ?A' {{{ Type@?i' }}} ?W' |- {{ ~?G ⊢ ~?A ⊆ ~?A' }} =>
        (on_all_hyp: fun H => apply soundness in H);
        destruct_conjs;
        functional_nbe_rewrite_clear;
        rename HA into W;
        rename HA' into W';
        assert {{ G ⊢ W : Type@i }} by (gen_presups; eassumption);
        assert {{ G ⊢ W' : Type@i }} by (gen_presups; eassumption);
        assert {{ G ⊢ W ⊆ W' }} by mauto;
        etransitivity;
        mauto
    | H: ~ (nf_subsumption ?W ?W') |- ~ {{ ~?G ⊢ ~?A ⊆ ~?A' }} =>
        contradict H;
        apply completeness_for_typ_subsumption in H;
        destruct_conjs;
        functional_nbe_rewrite_clear;
        eassumption
    end.

  #[tactic="impl_obl_tac"]
  Equations typ_subsumption_dec G i A (HA : {{ G ⊢ A : Type@i }}) A' (HA' : {{ G ⊢ A' : Type@i }}) : { {{ G ⊢ A ⊆ A' }} } + { ~ {{ G ⊢ A ⊆ A' }} } :=
  | G, i, A, HA, A', HA' =>
      let (W, HW) := nbe_impl G A {{{ Type@i }}} _ in
      let (W', HW') := nbe_impl G A' {{{ Type@i }}} _ in
      match nf_subsumption_dec W W' with
      | left _ => left _
      | right _ => right _
      end.
End typ_subsumption_dec.
