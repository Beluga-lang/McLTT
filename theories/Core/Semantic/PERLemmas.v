From Coq Require Import Lia PeanoNat Relations Program.Equality.
From Mcltt Require Import Base Domain Evaluate LibTactics PER Readback Syntax System.
From Equations Require Import Equations.

Lemma per_univ_sym : forall m m' i,
    {{ Dom m ≈ m' ∈ per_univ i }} -> {{ Dom m' ≈ m ∈ per_univ i }}
with per_elem_sym : forall m m' i R R' a a'
  (equiv_m_m' : {{ DF m ≈ m' ∈ per_univ_elem i ↘ R }})
  (equiv_m'_m : {{ DF m' ≈ m ∈ per_univ_elem i ↘ R' }}),
    {{ Dom a ≈ a' ∈ R }} <-> {{ Dom a' ≈ a ∈ R' }}.
Proof with mauto.
  all: intros *; try split.
  1: intro Hper_univ.
  2-3: intro Hper_elem.
  - destruct Hper_univ as [per_elem equiv_m_m'].
    autorewrite with per_univ_elem in equiv_m_m'.
    dependent induction equiv_m_m'; subst; only 1-2,4: solve [eexists; econstructor; mauto].
    (* Pi case *)
    destruct IHequiv_m_m' as [in_rel' IHequiv_a_a'].
    rewrite <- per_univ_elem_equation_1 in H, equiv_a_a'.
    (* (* One attempt *) *)
    (* unshelve epose (out_rel' := _ : forall c' c : domain, {{ Dom c' ≈ c ∈ in_rel' }} -> relation domain). *)
    (* { *)
    (*   intros * equiv_c'_c. *)
    (*   assert (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}) by (erewrite per_elem_sym; eassumption). *)
    (*   assert (rel_mod_eval (per_univ_elem i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel c c' equiv_c_c')) by mauto. *)
    (*   (* Failure point *) *)
    (*   destruct_last. *)
    (* } *)

    (* (* The other *) *)
    (* assert (exists (out_rel' : forall c' c : domain, {{ Dom c' ≈ c ∈ in_rel' }} -> relation domain), *)
    (*          forall (c' c : domain) (equiv_c'_c : {{ Dom c' ≈ c ∈ in_rel' }}), *)
    (*            rel_mod_eval (per_univ_elem i) B' d{{{ p' ↦ c' }}} B d{{{ p ↦ c }}} (out_rel' c' c equiv_c'_c)). *)
    (* { *)
    (*   (* This "eexists" is problematic *) *)
    (*   eexists. *)
    (*   intros. *)
    (*   assert (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}) by (erewrite per_elem_sym; eassumption). *)
    (*   assert (rel_mod_eval (per_univ_elem i) B d{{{ p ↦ c }}} B' d{{{ p' ↦ c' }}} (out_rel c c' equiv_c_c')) by mauto. *)
    (*   destruct_last. *)
    (*   econstructor; try eassumption. *)
    (* } *)
      
