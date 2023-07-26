Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.Domain.
Require Import Mcltt.Evaluation.
Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.

Reserved Notation "'Rf' A -- B ↘ C" (at level 90, B at next level, C at next level).
Reserved Notation "'Re' A -- B ↘ C" (at level 90, B at next level, C at next level).
Reserved Notation "'Rty' A -- B ↘ C" (at level 90, B at next level, C at next level).

Generalizable All Variables.
Print Grammar constr.

Inductive rf : nat -> Df -> Nf -> Prop :=
| rf_typ : `(Rty n -- A ↘ (W) ->
             Rf n -- ↓ (d_typ i) A ↘ W)
| rf_zero : `(Rf n -- ↓ d_nat d_zero ↘ nf_zero)
| rf_succ : `(Rf n -- ↓ d_nat a ↘ w ->
              Rf n -- ↓ d_nat (d_succ a) ↘ nf_succ w)
| rf_lam : `(a ∙d (↑ A (d_l n)) ↘ b ->
             ⟦ T ⟧ (p ↦ (↑ A (d_l n))) ↘ B ->
             Rf (1+n) -- ↓ B b ↘ w ->
             Rf n -- ↓ (d_pi A T p) a ↘ nf_lam w
             )
| rf_nat : `(Re n -- c ↘ u ->
            Rf n -- ↓ d_nat (↑ d_nat c) ↘ nf_ne u)
| rf_ne : `(Re n -- c' ↘ u ->
             Rf n -- ↓ (↑ A c) (↑ A' c') ↘ nf_ne u)
where "'Rf' A -- B ↘ C" := (rf A B C)
with re : nat -> Dn -> Ne -> Prop :=
| re_l : `(Re n -- d_l x ↘ ne_var (n - x - 1))
| re_app : `(Re n -- c ↘ u ->
             Rf n -- d ↘ w ->
             Re n -- (d_app c d) ↘ (ne_app u w))
| re_r : `((* Compute normal form of motive *)
           ⟦ T ⟧ (p ↦ ↑ d_nat (d_l n)) ↘ A ->
           Rty (1 + n) -- A ↘ W ->
           (* Compute normal form of base case *)
           ⟦ T ⟧ p ↦ d_zero ↘ A' ->
           Rf n -- ↓ A' a ↘ w ->
           (* Compute normal form of step case *)
           ⟦ t ⟧ (p ↦ ↑ d_nat (d_l n)) ↦ ↑ A (d_l (S n)) ↘ b ->
           ⟦ T ⟧ p ↦ d_succ (↑ d_nat (d_l n)) ↘ A'' ->
           Rf (2 + n) -- ↓ A'' b ↘ w' ->
           (* Compute normal form of the number *)
           Re n -- c ↘ u ->
           Re n -- (d_rec T a t p c) ↘ ne_rec W w w' u)
where "'Re' A -- B ↘ C" := (re A B C)
with rty : nat -> D -> Nf -> Prop :=
| rty_typ : `(Rty n -- (d_typ i) ↘ nf_typ i)
| rty_nat : `(Rty n -- d_nat ↘ nf_nat)
| rty_pi : `(Rty n -- A ↘ W ->
             ⟦ T ⟧ p ↦ (↑ A (d_l n)) ↘ B ->
             Rty (1 + n) -- B ↘ W' ->
             Rty n -- (d_pi A T p) ↘ nf_pi W W')
| rty_ne : `(Re n -- c ↘ V ->
             Rty n -- ↑ A c ↘ nf_ne V)
where "'Rty' A -- B ↘ C" := (rty A B C).  

Fixpoint Rf_det (n : nat) (d : Df) (w w': Nf) (eval_w : Rf n -- d ↘ w) (eval_w' : Rf n -- d ↘ w' ) : w = w'  
with Re_det (n : nat) (c : Dn) (u u' : Ne) (eval_u : Re n -- c ↘ u) (eval_u' : Re n -- c ↘ u') : u = u'
with Rty_det (n : nat) (A : D) (W W' : Nf) (eval_W : Rty n -- A ↘ W) (eval_W' : Rty n -- A ↘ W') : W = W'.
Proof.
  - inversion eval_w;inversion eval_w';(try congruence).
    -- subst.
       inversion H5.
       subst.
       apply (Rty_det _ _ _ _ H H3).
    -- subst.
       inversion H5.
       subst.
       rewrite (Rf_det _ _ _ _ H H3).
       reflexivity.
    -- subst.
       inversion H9.
       subst.
       rewrite (eval_det _ _ _ _ H0 H6) in H1.
       rewrite (ap_det _ _ _ _ H H5) in H1.
       rewrite (Rf_det _ _ _ _ H1 H7).
       reflexivity.
    -- subst.
       inversion H5.
       subst.
       rewrite (Re_det _ _ _ _ H H3).
       reflexivity.
    -- subst.
       inversion H5.
       subst.
       rewrite (Re_det _ _ _ _ H H3).
       reflexivity.
  - inversion eval_u;inversion eval_u';(try (subst;congruence)).
    -- subst.
       inversion H7.
       subst.
       rewrite (Re_det _ _ _ _ H H4).
       rewrite (Rf_det _ _ _ _ H0 H5).
       reflexivity.
    -- subst.
       inversion H19.
       subst.
       rewrite (eval_det _ _ _ _ H H10) in H0,H3.
       rewrite (Rty_det _ _ _ _ H0 H11).
       rewrite (eval_det _ _ _ _ H1 H12) in H2.
       rewrite (Rf_det _ _ _ _ H2 H13).
       rewrite (eval_det _ _ _ _ H4 H15) in H5.
       rewrite (eval_det _ _ _ _ H3 H14) in H5.
       rewrite (Rf_det _ _ _ _ H5 H16).
       rewrite (Re_det _ _ _ _ H6 H17).
       reflexivity.
  - inversion eval_W;inversion eval_W';(try congruence).
    -- subst. 
       inversion H9.
       subst.
       rewrite (eval_det _ _ _ _ H0 H6) in H1.
       rewrite (Rty_det _ _ _ _ H H5).
       rewrite (Rty_det _ _ _ _ H1 H7).
       reflexivity.
    -- subst.
       inversion H5.
       subst.
       rewrite (Re_det _ _ _ _ H H3).
       reflexivity.
Qed.  

Record nbe_envs (n : nat) (p : Env) (t T : exp) (w : Nf) : Set := mk_nbe_env
 {
   val_t : D
 ; val_T : D
 ; eval_t : ⟦ t ⟧ p ↘ val_t
 ; eval_T : ⟦ T ⟧ p ↘ val_T
 ; down_t : Rf n -- ↓ val_T val_t ↘ w
 }.                                      


Inductive InitEnvs : Ctx -> Env -> Set :=
| base : InitEnvs nil d_emp
| s_cons : `(InitEnvs Γ p ->
             ⟦ T ⟧ p ↘ A ->
             InitEnvs (T :: Γ) (p ↦ (↑ A (d_l (length Γ))))
             )
.

Record NbE (Γ : Ctx) (t T : exp) (w : Nf) : Set := mk_nbe
 {
   envs : Env
 ; init : InitEnvs Γ envs
 ; nbe  : nbe_envs (length Γ) envs t T w
 }.

Lemma InitEnvs_det (Γ : Ctx) (p p' : Env) : InitEnvs Γ p -> InitEnvs Γ p' -> p = p' .
Proof.
  intros.
  generalize dependent p'.
  dependent induction H.
  - intros.
    inversion H0.
    reflexivity.
  - intros.
    inversion H0.
    pose proof (IHInitEnvs _ H3).
    rewrite H6 in d.
    rewrite (eval_det _ _ _ _ d H5), H6.
    reflexivity.
Qed.  

Lemma NbE_det : `(NbE Γ t T w -> NbE Γ t T w' ->
                  w = w').
Proof.
  intros.
  inversion H.
  inversion H0.
  rewrite (InitEnvs_det _ _ _ init0 init1) in nbe0.
  inversion nbe0.
  inversion nbe1.
  rewrite (eval_det _ _ _ _ eval_t0 eval_t1), (eval_det _ _ _ _ eval_T0 eval_T1) in down_t0.
  apply (Rf_det _ _ _ _ down_t0 down_t1).  
Qed.  
