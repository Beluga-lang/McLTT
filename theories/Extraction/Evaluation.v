From Equations Require Import Equations.

From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Semantic Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

Inductive eval_exp_order : exp -> env -> Prop :=
| eeo_typ :
  `( eval_exp_order {{{ Type@i }}} p )
| eeo_var :
  `( eval_exp_order {{{ # x }}} p )
| eeo_nat :
  `( eval_exp_order {{{ ℕ }}} p )
| eeo_zero :
  `( eval_exp_order {{{ zero }}} p )
| eeo_succ :
  `( eval_exp_order {{{ M }}} p ->
     eval_exp_order {{{ succ M }}} p )
| eeo_natrec :
  `( eval_exp_order M p ->
     (forall m, {{ ⟦ M ⟧ p ↘ m }} -> eval_natrec_order A MZ MS m p) ->
     eval_exp_order {{{ rec M return A | zero -> MZ | succ -> MS end }}} p )
| eeo_pi :
  `( eval_exp_order A p ->
     eval_exp_order {{{ Π A B }}} p )
| eeo_fn :
  `( eval_exp_order {{{ λ A M }}} p )
| eeo_app :
  `( eval_exp_order M p ->
     eval_exp_order N p ->
     (forall m n, {{ ⟦ M ⟧ p ↘ m }} -> {{ ⟦ N ⟧ p ↘ n }} -> eval_app_order m n) ->
     eval_exp_order {{{ M N }}} p )
| eeo_sub :
  `( eval_sub_order σ p ->
     (forall p', {{ ⟦ σ ⟧s p ↘ p' }} -> eval_exp_order M p') ->
     eval_exp_order {{{ M[σ] }}} p )

with eval_natrec_order : exp -> exp -> exp -> domain -> env -> Prop :=
| eno_zero :
  `( eval_exp_order MZ p ->
     eval_natrec_order A MZ MS d{{{ zero }}} p )
| eno_succ :
  `( eval_natrec_order A MZ MS b p ->
     (forall r, {{ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} -> eval_exp_order {{{ MS }}} d{{{ p ↦ b ↦ r }}}) ->
     eval_natrec_order A MZ MS d{{{ succ b }}} p )
| eno_neut :
  `( eval_exp_order MZ p ->
     eval_exp_order A d{{{ p ↦ ⇑ a m }}} ->
     eval_natrec_order A MZ MS d{{{ ⇑ a m }}} p )

with eval_app_order : domain -> domain -> Prop :=
| eao_fn :
  `( eval_exp_order M d{{{ p ↦ n }}} ->
     eval_app_order d{{{ λ p M }}} n )
| eao_neut :
  `( eval_exp_order B d{{{ p ↦ n }}} ->
     eval_app_order d{{{ ⇑ (Π a p B) m }}} n )

with eval_sub_order : sub -> env -> Prop :=
| eso_id :
  `( eval_sub_order {{{ Id }}} p )
| eso_weaken :
  `( eval_sub_order {{{ Wk }}} p )
| eso_extend :
  `( eval_sub_order σ p ->
     eval_exp_order M p ->
     eval_sub_order {{{ σ ,, M }}} p )
| eso_compose :
  `( eval_sub_order τ p ->
     (forall p', {{ ⟦ τ ⟧s p ↘ p' }} -> eval_sub_order σ p') ->
     eval_sub_order {{{ σ ∘ τ }}} p ).

#[local]
Hint Constructors eval_exp_order eval_natrec_order eval_app_order eval_sub_order : mcltt.

Lemma eval_exp_order_sound : forall m p a,
    {{ ⟦ m ⟧ p ↘ a }} ->
    eval_exp_order m p
with eval_natrec_order_sound : forall A MZ MS m p r,
    {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} ->
    eval_natrec_order A MZ MS m p
with eval_app_order_sound: forall m n r,
  {{ $| m & n |↘ r }} ->
  eval_app_order m n
with eval_sub_order_sound: forall σ p p',
  {{ ⟦ σ ⟧s p ↘ p' }} ->
  eval_sub_order σ p.
Proof with (econstructor; intros; functional_eval_rewrite_clear; eauto).
  - clear eval_exp_order_sound; induction 1...
  - clear eval_natrec_order_sound; induction 1...
  - clear eval_app_order_sound; induction 1...
  - clear eval_sub_order_sound; induction 1...
Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_natrec_order_sound eval_app_order_sound eval_sub_order_sound : mcltt.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : eval_exp_order _ _ |- _ => progressive_invert H
  | H : eval_natrec_order _ _ _ _ _ |- _ => progressive_invert H
  | H : eval_app_order _ _ |- _ => progressive_invert H
  | H : eval_sub_order _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; eauto.

#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations eval_exp_impl m p (H : eval_exp_order m p) : { d | eval_exp m p d } by struct H :=
| {{{ Type@i }}}, p, H => exist _ d{{{ 𝕌@i }}} _
| {{{ #x }}}    , p, H => exist _ (p x) _
| {{{ ℕ }}}     , p, H => exist _ d{{{ ℕ }}} _
| {{{ zero }}}  , p, H => exist _ d{{{ zero }}} _
| {{{ succ m }}}, p, H =>
    let (r , Hr) := eval_exp_impl m p _ in
    exist _ d{{{ succ r }}} _
| {{{ rec M return A | zero -> MZ | succ -> MS end }}}, p, H =>
    let (m , Hm) := eval_exp_impl M p _ in
    let (r, Hr)  := eval_natrec_impl A MZ MS m p _ in
    exist _ r _
| {{{ Π A B }}} , p, H =>
    let (r , Hr) := eval_exp_impl A p _ in
    exist _ d{{{ Π r p B }}} _
| {{{ λ A M }}} , p, H => exist _ d{{{ λ p M }}} _
| {{{ M N }}}   , p, H =>
    let (m , Hm) := eval_exp_impl M p _ in
    let (n , Hn) := eval_exp_impl N p _ in
    let (a, Ha) := eval_app_impl m n _ in
    exist _ a _
| {{{ M[σ] }}}  , p, H =>
    let (p', Hp') := eval_sub_impl σ p _ in
    let (m, Hm) := eval_exp_impl M p' _ in
    exist _ m _

with eval_natrec_impl A MZ MS m p (H : eval_natrec_order A MZ MS m p) : { d | eval_natrec A MZ MS m p d } by struct H :=
| A, MZ, MS, d{{{ zero }}}  , p, H =>
    let (mz, Hmz) := eval_exp_impl MZ p _ in
    exist _ mz _
| A, MZ, MS, d{{{ succ m }}}, p, H =>
    let (mr, Hmr) := eval_natrec_impl A MZ MS m p _ in
    let (r, Hr) := eval_exp_impl MS d{{{ p ↦ m ↦ mr }}} _ in
    exist _ r _
| A, MZ, MS, d{{{ ⇑ a m }}} , p, H =>
    let (mz, Hmz) := eval_exp_impl MZ p _ in
    let (mA, HmA) := eval_exp_impl A d{{{ p ↦ ⇑ a m }}} _ in
    exist _ d{{{ ⇑ mA (rec m under p return A | zero -> mz | succ -> MS end) }}} _

with eval_app_impl m n (H : eval_app_order m n) : { d | eval_app m n d } by struct H :=
| d{{{ λ p M }}}        , n, H =>
    let (m, Hm) := eval_exp_impl M d{{{ p ↦ n }}} _ in
    exist _ m _
| d{{{ ⇑ (Π a p B) m }}}, n, H =>
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ n }}} _ in
    exist _ d{{{ ⇑ b (m (⇓ a n)) }}} _

with eval_sub_impl s p (H : eval_sub_order s p) : { p' | eval_sub s p p' } by struct H :=
| {{{ Id }}}, p, H => exist _ p _
| {{{ Wk }}}, p, H => exist _ d{{{ p↯ }}} _
| {{{ s ,, M }}}, p, H =>
    let (p', Hp') := eval_sub_impl s p _ in
    let (m, Hm) := eval_exp_impl M p _ in
    exist _ d{{{ p' ↦ m }}} _
| {{{ s ∘ τ }}}, p, H =>
    let (p', Hp') := eval_sub_impl τ p _ in
    let (p'', Hp'') := eval_sub_impl s p' _ in
    exist _ p'' _.

Extraction Inline eval_exp_impl_functional
  eval_natrec_impl_functional
  eval_app_impl_functional
  eval_sub_impl_functional.

(** The definitions of [eval_*_impl] already come with soundness proofs,
    so we only need to prove completeness. However, the completeness
    is also obvious from the soundness of eval orders and functional
    nature of eval. *)

#[local]
Ltac functional_eval_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_eval_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma eval_exp_impl_complete : forall M p m,
    {{ ⟦ M ⟧ p ↘ m }} ->
    exists H H', eval_exp_impl M p H = exist _ m H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_natrec_impl_complete : forall A MZ MS m p r,
    {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ p ↘ r }} ->
    exists H H', eval_natrec_impl A MZ MS m p H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_app_impl_complete : forall m n r,
    {{ $| m & n |↘ r }} ->
    exists H H', eval_app_impl m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_sub_impl_complete : forall σ p p',
    {{ ⟦ σ ⟧s p ↘ p' }} ->
    exists H H', eval_sub_impl σ p H = exist _ p' H'.
Proof.
  intros; functional_eval_complete.
Qed.
