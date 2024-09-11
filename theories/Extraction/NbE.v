From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Export NbE.
From Mcltt.Extraction Require Import Evaluation Readback.
From Equations Require Import Equations.
Import Domain_Notations.

Generalizable All Variables.

Inductive initial_env_order : ctx -> Prop :=
| ie_nil : initial_env_order nil
| ie_cons :
  `( initial_env_order Γ ->
     (forall p, initial_env Γ p ->
           eval_exp_order A p) ->
     initial_env_order (A :: Γ)).

#[local]
Hint Constructors initial_env_order : mcltt.

Lemma initial_env_order_sound : forall Γ p,
    initial_env Γ p ->
    initial_env_order Γ.
Proof with (econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear; mauto).
  induction 1...
Qed.

#[local]
Hint Resolve initial_env_order_sound : mcltt.

Derive Signature for initial_env_order.

Section InitialEnvImpl.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : initial_env_order _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl G (H : initial_env_order G) : { p | initial_env G p } by struct H :=
  | nil, H => exist _ empty_env _
  | cons A G, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (a, Ha) := eval_exp_impl A p _ in
      exist _ d{{{ p ↦ ⇑! a (length G) }}} _.

End InitialEnvImpl.

(** The definitions of [initial_env_impl] already come with soundness proofs,
    so we only need to prove completeness. However, the completeness
    is also obvious from the soundness of eval orders and functional
    nature of initial_env. *)

Lemma initial_env_impl_complete : forall G p,
    initial_env G p ->
    exists H H', initial_env_impl G H = exist _ p H'.
Proof.
  intros.
  assert (Horder : initial_env_order G) by mauto.
  exists Horder.
  destruct (initial_env_impl G Horder).
  functional_initial_env_rewrite_clear.
  eexists; reflexivity.
Qed.

(** A similar approach works for nbe implementations.
    However, as we have 2 implementations (each for [nbe] and [nbe_ty]),
    We define a tactic to deal with both cases. *)

Ltac functional_nbe_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_nbe_rewrite_clear;
          eexists; reflexivity
      end
  end.

Inductive nbe_order G M A : Prop :=
| nbe_order_run :
  `( initial_env_order G ->
     (forall p, initial_env G p ->
           eval_exp_order A p) ->
     (forall p, initial_env G p ->
           eval_exp_order M p) ->
     (forall p a m,
         initial_env G p ->
         {{ ⟦ A ⟧ p ↘ a }} ->
         {{ ⟦ M ⟧ p ↘ m }} ->
         read_nf_order (length G) d{{{ ⇓ a m }}}) ->
     nbe_order G M A ).

#[local]
Hint Constructors nbe_order : mcltt.

Lemma nbe_order_sound : forall G M A w,
    nbe G M A w ->
    nbe_order G M A.
Proof with (econstructor; intros;
            functional_initial_env_rewrite_clear;
            functional_eval_rewrite_clear;
            functional_read_rewrite_clear;
            mauto).
  induction 1...
Qed.

#[local]
Hint Resolve nbe_order_sound : mcltt.

Section NbEDef.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : nbe_order _ _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_impl G M A (H : nbe_order G M A) : { w | nbe G M A w } by struct H :=
  | G, M, A, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (a, Ha) := eval_exp_impl A p _ in
      let (m, Hm) := eval_exp_impl M p _ in
      let (w, Hw) := read_nf_impl (length G) d{{{ ⇓ a m }}} _ in
      exist _ w _.

End NbEDef.

Lemma nbe_impl_complete : forall G M A w,
    nbe G M A w ->
    exists H H', nbe_impl G M A H = exist _ w H'.
Proof.
  intros; functional_nbe_complete.
Qed.

Inductive nbe_ty_order G A : Prop :=
| nbe_ty_order_run :
  `( initial_env_order G ->
     (forall p, initial_env G p ->
           eval_exp_order A p) ->
     (forall p a,
         initial_env G p ->
         {{ ⟦ A ⟧ p ↘ a }} ->
         read_typ_order (length G) a) ->
     nbe_ty_order G A ).

#[local]
Hint Constructors nbe_ty_order : mcltt.

Lemma nbe_ty_order_sound : forall G A w,
    nbe_ty G A w ->
    nbe_ty_order G A.
Proof with (econstructor; intros;
            functional_initial_env_rewrite_clear;
            functional_eval_rewrite_clear;
            functional_read_rewrite_clear;
            mauto).
  induction 1...
Qed.

#[local]
Hint Resolve nbe_ty_order_sound : mcltt.

Section NbETyDef.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : nbe_ty_order _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_impl G A (H : nbe_ty_order G A) : { w | nbe_ty G A w } by struct H :=
  | G, A, H =>
      let (p, Hp) := initial_env_impl G _ in
      let (a, Ha) := eval_exp_impl A p _ in
      let (w, Hw) := read_typ_impl (length G) a _ in
      exist _ w _.

End NbETyDef.

Lemma nbe_ty_impl_complete : forall G A w,
    nbe_ty G A w ->
    exists H H', nbe_ty_impl G A H = exist _ w H'.
Proof.
  intros; functional_nbe_complete.
Qed.
