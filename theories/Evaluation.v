Require Import Mcltt.Syntax.
Require Import Mcltt.System.
Require Import Mcltt.Domain.
Require Import Unicode.Utf8.
Reserved Notation "A ∙d B ↘ C" (at level 90).
Reserved Notation "'rec∙' A , B , C , D , E ↘ F" (at level 90, B at next level, C at next level, D at next level, E at next level, F at next level).
Reserved Notation "⟦ A ⟧ B ↘ C" (at level 90).
Reserved Notation "⟦ A ⟧s B ↘ C" (at level 90).

Generalizable All Variables.

Inductive d_app_eval : D -> D -> D -> Set :=
| d_app_lam : `(⟦ t ⟧ (p ↦ a) ↘ b ->
              (d_lam t p) ∙d a ↘ b)
| d_app_app : `(⟦ T ⟧ (p ↦ a) ↘ B ->
                (↑ (d_pi A T p) c) ∙d a ↘ (↑ B (d_app c (↓ A a))))
where "A ∙d B ↘ C" := (d_app_eval A B C)
with d_rec_eval : Typ -> D -> exp -> Env -> D -> D -> Set :=
| d_rec_zero : `(rec∙ T , a , t , p , d_zero ↘ a)
| d_rec_succ : `(rec∙ T , a , t , p , b ↘ b' ->
                 ⟦ t ⟧ (p ↦ b ↦ b') ↘ a' ->
                 rec∙ T , a , t , p , (d_succ b) ↘ a')
| d_rec_rec : `(⟦ T ⟧ (p ↦ (↑ d_nat c)) ↘ (↑ A (d_rec T a t p c)) ->
            rec∙ T ,a , t , p , (↑ d_nat c) ↘ ↑ A (d_rec T a t p c))
where "'rec∙' A , B , C , D , E ↘ F" := (d_rec_eval A B C D E F)
with d_tm_eval : exp -> Env -> D -> Set :=
| d_eval_nat : `(⟦ a_nat ⟧ p ↘ d_nat)
| d_eval_pi : `(⟦ M ⟧ p ↘ A ->
                ⟦ a_pi M T ⟧ p ↘ (d_pi A T p) )
| d_eval_typ : `(⟦ typ i ⟧ p ↘ d_typ i)
| d_eval_var : `(⟦ a_var n ⟧ p ↘ (d_lookup p n))
| d_eval_zero : `(⟦ a_zero ⟧ p ↘ d_zero)
| d_eval_succ : `(⟦ t ⟧ p ↘ a ->
                  ⟦ a_succ t ⟧ p ↘ d_succ a)
(*| d_eval_rec : `(⟦ s ⟧ p ↘ a ->
                 ⟦ t ⟧ p ↘ b ->
                 rec∙ T a r p b ↘ a' ->
                 ⟦ a_rec T s r t ⟧ p ↘ a') *)
| d_eval_lam : `(⟦ a_fn T t ⟧ p ↘ d_lam t p) 
| d_eval_app : `(⟦ r ⟧ p ↘ f ->
                 ⟦ s ⟧ p ↘ a ->
                 f ∙d a ↘ b ->
                 ⟦a_app r s ⟧ p ↘ b)
| d_eval_sub : `(⟦ σ ⟧s p ↘ p' ->
                 ⟦ t ⟧ p' ↘ a ->
                 ⟦ a_sub t σ ⟧ p ↘ a)
where "⟦ A ⟧ B ↘ C" := (d_tm_eval A B C)
with d_sb_eval : Sb -> Env -> Env -> Set :=
| d_sb_eval_id : `(⟦ a_id ⟧s p ↘ p)
| d_sb_eval_wk : `(⟦ a_weaken ⟧s p ↘ (d_drop p))
| d_sb_eval_ext : `(⟦ σ ⟧s p ↘ p' ->
                    ⟦ t ⟧ p ↘ a ->
                    ⟦ σ ,, t ⟧s p ↘ (p' ↦ a))
| d_sb_eval_comp: `(⟦ τ ⟧s p ↘ p' ->
                    ⟦ σ ⟧s p' ↘ p'' ->
                    ⟦ σ ∙ τ ⟧s p ↘ p'')
where "⟦ A ⟧s B ↘ C" := (d_sb_eval A B C).  

Fixpoint ap_det (f a b b' : D) (eval_b : f ∙d a ↘ b) (eval_b' : f ∙d a ↘ b') {struct eval_b}: b = b'
with rec_det (T : Typ) (r : exp) (p : Env) (a b a' b' : D)  (eval_a': rec∙ T , a , r , p , b ↘ a') (eval_b' : rec∙ T , a , r, p , b ↘ b') {struct eval_a'} : a' = b'
with eval_det (t : exp) (p : Env) (a b : D) (eval_a : ⟦ t ⟧ p ↘ a) (eval_b : ⟦ t ⟧ p ↘ b) {struct eval_a} : a = b
with eval_sb_det (σ : Sb) (p p' p'' : Env) (eval_p': ⟦ σ ⟧s p ↘ p') (eval_p'': ⟦ σ ⟧s p ↘ p'') : p' = p''                                                                             
.
Proof.
  - inversion eval_b.
    inversion eval_b'.
    -- rewrite <- H0 in H4.
       injection H4.
       intros.
       rewrite H7, H8 in H3.
       eapply (eval_det _ _ _ _ H H3).
    -- rewrite <- H0 in H4.
       inversion H4.
    -- inversion eval_b'.
       rewrite <- H0 in H4.
       inversion H4.
       rewrite <- H0 in H4.
       inversion H4.
       rewrite H9,H10 in H3.
       rewrite (eval_det _ _ _ _ H H3).
       reflexivity.
  - inversion eval_a'.
    inversion eval_b'.
    -- congruence.
    -- congruence.
    -- congruence.
    -- inversion eval_b'.
       --- congruence.
       --- rewrite <- H13 in H5.
           injection H5.
           intros.
           rewrite H15 in H0, H.
           pose proof (rec_det _ _ _ _ _ _ _ H H7).
           rewrite <- H16 in H8.
           eapply (eval_det _ _ _ _ H0 H8).
       --- congruence.
    -- inversion eval_b'.
       --- congruence.
       --- congruence.
       --- rewrite <- H11 in H4.
           injection H4;intros.
           rewrite H13.
           rewrite H13 in H.
           pose proof (eval_det _ _ _ _ H H6).
           injection H14;intro.
           rewrite H15.
           reflexivity.
  - inversion eval_a;inversion eval_b;(try congruence).
    -- rewrite <- H0 in H4.
       injection H4;intros.
       rewrite <- H8 in H.
       pose proof (eval_det _ _ _ _ H H3).
       congruence.
    -- rewrite <- H0 in H4.
       inversion H4.
       rewrite <- H8 in H.
       pose proof (eval_det _ _ _ _ H H3).
       rewrite H7.
       congruence.
    -- rewrite <- H8 in H2.
       inversion H2.
       rewrite <- H12 in H5.
       rewrite <- H13 in H6.
       pose proof (eval_det _ _ _ _ H H5).
       pose proof (eval_det _ _ _ _ H0 H6).
       rewrite H14 in H1.
       rewrite <- H11 in H7.
       eapply (ap_det _ _ _ _ H1 H7).
    -- rewrite <- H6 in H1.
       inversion H1.
       rewrite H10 in H0.
       rewrite H11 in H.
       rewrite <- (eval_sb_det _ _ _ _ H H4) in H5.
       eapply (eval_det _ _ _ _ H0 H5).
  - inversion eval_p';inversion eval_p'';(try congruence).
    -- rewrite <- H6 in H1.
       inversion H1.
       rewrite H10 in H.
       rewrite H11 in H0.
       rewrite (eval_sb_det _ _ _ _ H H4).
       rewrite (eval_det _ _ _ _ H0 H5).
       reflexivity.
    -- rewrite <- H6 in H1.
       inversion H1.
       rewrite H10 in H0.
       rewrite H11 in H.
       rewrite (eval_sb_det _ _ _ _ H H4) in H0.
       exact (eval_sb_det _ _ _ _ H0 H5).
Qed.  
