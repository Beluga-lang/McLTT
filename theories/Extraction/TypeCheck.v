From Coq Require Import Morphisms_Relations.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import
  Completeness
  Completeness.Consequences.Inversions
  Completeness.Consequences.Types
  Completeness.FundamentalTheorem
  Completeness.LogicalRelation
  NbE
  Semantic.Consequences
  Semantic.Realizability
  Soundness
  SystemOpt.
From Mcltt.Extraction Require Import NbE.
From Equations Require Import Equations.
Import Domain_Notations.

Definition sumbool_failable_bind {A B} (ab : {A} + {B}) {C D : Prop} (fail : B -> D) (next : A -> {C} + {D}) :=
  match ab with
  | left a => next a
  | right b => right (fail b)
  end.

Notation "'let*b' a ':=' ab 'while' fail 'in' next" := (sumbool_failable_bind ab fail (fun a => next)) (at level 0, a pattern, next at level 10, right associativity, only parsing).
Notation "'pureb' a" := (left a) (at level 0, only parsing).

Definition sumor_failable_bind {A B} (ab : A + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> C + {D}) :=
  match ab with
  | inleft a => next a
  | inright b => inright (fail b)
  end.

Notation "'let*o' a ':=' ab 'while' fail 'in' next" := (sumor_failable_bind ab fail (fun a => next)) (at level 0, a pattern, next at level 10, right associativity, only parsing).
Notation "'pureo' a" := (inleft a) (at level 0, only parsing).

Definition sumbool_sumor_failable_bind {A B} (ab : {A} + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> C + {D}) :=
  match ab with
  | left a => next a
  | right b => inright (fail b)
  end.

Notation "'let*b->o' a ':=' ab 'while' fail 'in' next" := (sumbool_sumor_failable_bind ab fail (fun a => next)) (at level 0, a pattern, next at level 10, right associativity, only parsing).

Definition sumor_sumbool_failable_bind {A B} (ab : A + {B}) {C} {D : Prop} (fail : B -> D) (next : A -> {C} + {D}) :=
  match ab with
  | inleft a => next a
  | inright b => right (fail b)
  end.

Notation "'let*o->b' a ':=' ab 'while' fail 'in' next" := (sumor_sumbool_failable_bind ab fail (fun a => next)) (at level 0, a pattern, next at level 10, right associativity, only parsing).

(* Section nf_subsumption_dec. *)
(*   #[local] *)
(*   Ltac impl_obl_tac := *)
(*     match goal with *)
(*     | |- nf_subsumption _ _ => mauto 2 *)
(*     | A := _ : nf |- ~ (nf_subsumption _ _) => *)
(*         let H := fresh "H" in *)
(*         subst A; intro H; dependent destruction H; congruence *)
(*     | |- ~ (nf_subsumption _ _) => *)
(*         let H := fresh "H" in *)
(*         intro H; dependent destruction H; lia *)
(*     end. *)

(*   #[tactic=impl_obl_tac] *)
(*   Equations nf_subsumption_dec A A' : {nf_subsumption A A'} + {~ nf_subsumption A A'} := *)
(*   | n{{{ Type@i }}}, n{{{ Type@j }}} => *)
(*       let*b _ := Compare_dec.le_lt_dec i j while _ in *)
(*       pureb _ *)
(*   (* Here we have a separate clause for n{{{ Type@i }}} so that we can extract a more efficient code *) *)
(*   | n{{{ Type@i }}}, _ => right _ *)
(*   | A, A' => *)
(*       let*b _ := nf_eq_dec A A' while _ in *)
(*       pureb _. *)
(* End nf_subsumption_dec. *)

(* Section conversion_dec. *)
(*   #[local] *)
(*   Ltac impl_obl_tac := *)
(*     match goal with *)
(*     | |- nbe_order _ _ _ => *)
(*         (on_all_hyp: fun H => apply soundness in H); *)
(*         destruct_conjs; *)
(*         eapply nbe_order_sound; eassumption *)
(*     | |- _ <> _ -> ~ {{ ~_ ⊢ ~_ ≈ ~_ : ~_ }} => *)
(*         intros ? ?%completeness; *)
(*         destruct_conjs; *)
(*         functional_nbe_rewrite_clear; *)
(*         congruence *)
(*     | |- {{ ~_ ⊢ ~_ ≈ ~_ : ~_ }} => *)
(*         (on_all_hyp: fun H => apply soundness in H); *)
(*         destruct_conjs; *)
(*         functional_nbe_rewrite_clear; *)
(*         mautosolve *)
(*     end. *)
(*   #[tactic="impl_obl_tac"] *)
(*   Equations conversion_dec G A M (HM : {{ G ⊢ M : A }}) M' (HM' : {{ G ⊢ M' : A }}) : { {{ G ⊢ M ≈ M' : A }} } + { ~ {{ G ⊢ M ≈ M' : A }} } := *)
(*   | G, A, M, HM, M', HM' => *)
(*       let (W, HW) := nbe_impl G M A _ in *)
(*       let (W', HW') := nbe_impl G M' A _ in *)
(*       let*b _ := nf_eq_dec W W' while _ in *)
(*       pureb _. *)
(* End conversion_dec. *)

(* Section typ_subsumption_dec. *)
(*   #[local] *)
(*   Ltac impl_obl_tac := *)
(*     match goal with *)
(*     | |- nbe_order ?G ?M ?A => *)
(*         (on_all_hyp: fun H => apply soundness in H); *)
(*         destruct_conjs; *)
(*         eapply nbe_order_sound; eassumption *)
(*     | H: nbe ?G ?A {{{ Type@?i }}} ?W, H': nbe ?G ?A' {{{ Type@?i' }}} ?W' |- {{ ~?G ⊢ ~?A ⊆ ~?A' }} => *)
(*         (on_all_hyp: fun H => apply soundness in H); *)
(*         destruct_conjs; *)
(*         functional_nbe_rewrite_clear; *)
(*         rename HA into W; *)
(*         rename HA' into W'; *)
(*         assert {{ G ⊢ W : Type@i }} by (gen_presups; eassumption); *)
(*         assert {{ G ⊢ W' : Type@i }} by (gen_presups; eassumption); *)
(*         assert {{ G ⊢ W ⊆ W' }} by mauto; *)
(*         etransitivity; *)
(*         mautosolve *)
(*     | |- ~ (nf_subsumption ?W ?W') -> ~ {{ ~?G ⊢ ~?A ⊆ ~?A' }} => *)
(*         let H := fresh "H" in *)
(*         intro H; *)
(*         contradict H; *)
(*         apply completeness_for_typ_subsumption in H; *)
(*         destruct_conjs; *)
(*         functional_nbe_rewrite_clear; *)
(*         eassumption *)
(*     end. *)

(*   #[tactic="impl_obl_tac"] *)
(*   Equations typ_subsumption_dec G i A (HA : {{ G ⊢ A : Type@i }}) A' (HA' : {{ G ⊢ A' : Type@i }}) : { {{ G ⊢ A ⊆ A' }} } + { ~ {{ G ⊢ A ⊆ A' }} } := *)
(*   | G, i, A, HA, A', HA' => *)
(*       let (W, HW) := nbe_impl G A {{{ Type@i }}} _ in *)
(*       let (W', HW') := nbe_impl G A' {{{ Type@i }}} _ in *)
(*       let*b _ := nf_subsumption_dec W W' while _ in *)
(*       pureb _. *)
(* End typ_subsumption_dec. *)

Section lookup.
  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | |- ~_ => intro
    | H: {{ ⊢ ~_, ~_ }} |- _ => inversion_clear H
    | H: {{ # _ : ~_ ∈ ⋅ }} |- _ => inversion_clear H
    | H: {{ # (S _) : ~_ ∈ ~_, ~_ }} |- _ => inversion_clear H
    end.

  #[local]
  Ltac impl_obl_tac :=
    intros;
    repeat impl_obl_tac1;
    intuition (mauto 4).

  #[tactic="impl_obl_tac"]
  Equations lookup G (HG : {{ ⊢ G }}) x : { A | {{ #x : A ∈ G }} } + { forall A, ~ {{ #x : A ∈ G }} } :=
  | {{{ G, A }}}, HG, x with x => {
    | 0 => pureo (exist _ {{{ A[Wk] }}} _)
    | S x' =>
        let*o (exist _ B _) := lookup G _ x' while _ in
        pureo (exist _ {{{ B[Wk] }}} _)
    }
  | {{{ ⋅ }}}, HG, x => inright _.
End lookup.

Axiom TODO : False.

Tactic Notation "TODOtac" string(_unused) := exfalso; exact TODO.

Section pi_conversion.
  #[local]
  Ltac impl_obl_tac :=
    simpl in *;
    match goal with
    | |- nbe_order ?G ?M ?A =>
        (on_all_hyp: fun H => apply soundness in H);
        destruct_conjs;
        eapply nbe_order_sound; eassumption
    | H: nbe ?G ?C {{{ Type@?i }}} ?W |- forall j A B, ~ {{ ~?G ⊢ Π A B ≈ ~?C : Type@j }} =>
        intros * ?;
        (on_all_hyp: fun H => apply soundness in H);
        destruct_conjs;
        functional_nbe_rewrite_clear;
        assert {{ G ⊢ Π A B ≈ W : Type@(max i j) }} by mauto;
        assert {{ G ⊨ Π A B ≈ W : Type@(max i j) }} as [env_relG] by mauto using completeness_fundamental_exp_eq;
        destruct_conjs;
        assert (exists p p', initial_env G p /\ initial_env G p' /\ {{ Dom p ≈ p' ∈ env_relG }}) as [p [? [? []]]] by eauto using per_ctx_then_per_env_initial_env;
        functional_initial_env_rewrite_clear;
        (on_all_hyp: destruct_rel_by_assumption env_relG);
        destruct_by_head rel_typ;
        invert_rel_typ_body;
        destruct_by_head rel_exp;
        invert_rel_typ_body;
        destruct_conjs;
        match_by_head1 per_univ_elem invert_per_univ_elem
    | _ => idtac "upwg"; show_hyps; show_goal
    end.

  #[tactic="impl_obl_tac"]
  Equations pi_conversion G i C (HC : {{ G ⊢ C : Type@i }}) : { '(A, B) | {{ G ⊢ Π A B ≈ C : Type@i }} } + { forall j A B, ~{{ G ⊢ Π A B ≈ C : Type@j }} } :=
  | G, i, C, HC with nbe_impl G C {{{ Type@i }}} _ => {
    | (exist _ n{{{ Π W1 W2 }}} _) => pureo (exist _ (nf_to_exp W1, nf_to_exp W2) _)
    | _ => inright _
    }
  .

  Next Obligation.
    (on_all_hyp: fun H => apply soundness in H).
    destruct_conjs.
    functional_nbe_rewrite_clear.
    mauto.
  Qed.

  Next Obligation.
    TODOtac "Pi is never equivalent to a neutral term".
  Qed.
End pi_conversion.

Section type_check.
  Inductive type_check_order : exp -> Prop :=
  | tc_typ : forall {i}, min_level_infer_order {{{ Type@i }}} -> type_check_order {{{ Type@i }}}
  | tc_nat : min_level_infer_order {{{ ℕ }}} -> type_check_order {{{ ℕ }}}
  | tc_zero : type_check_order {{{ zero }}}
  | tc_succ : forall {M}, type_check_order M -> type_check_order {{{ succ M }}}
  | tc_natrec : forall {A MZ MS M}, min_type_infer_order {{{ rec M return A | zero -> MZ | succ -> MS end }}} -> type_check_order {{{ rec M return A | zero -> MZ | succ -> MS end }}}
  | tc_pi : forall {A B}, min_level_infer_order {{{ Π A B }}} -> type_check_order {{{ Π A B }}}
  | tc_fn : forall {A M}, min_level_infer_order A -> type_check_order M -> type_check_order {{{ λ A M }}}
  | tc_app : forall {M N}, min_type_infer_order {{{ M N }}} -> type_check_order {{{ M N }}}
  | tc_vlookup : forall {x}, min_type_infer_order {{{ #x }}} -> type_check_order {{{ #x }}}
  with min_type_infer_order : exp -> Prop :=
  | mti_typ : forall {i}, min_level_infer_order {{{ Type@i }}} -> min_type_infer_order {{{ Type@i }}}
  | mti_nat : min_level_infer_order {{{ ℕ }}} -> min_type_infer_order {{{ ℕ }}}
  | mti_zero : min_type_infer_order {{{ zero }}}
  | mti_succ : forall {M}, type_check_order M -> min_type_infer_order {{{ succ M }}}
  | mti_natrec : forall {A MZ MS M}, type_check_order M -> min_level_infer_order A -> type_check_order MZ -> type_check_order MS -> min_type_infer_order {{{ rec M return A | zero -> MZ | succ -> MS end }}}
  | mti_pi : forall {A B}, min_level_infer_order {{{ Π A B }}} -> min_type_infer_order {{{ Π A B }}}
  | mti_fn : forall {A M}, min_level_infer_order A -> min_type_infer_order M -> min_type_infer_order {{{ λ A M }}}
  | mti_app : forall {M N}, min_type_infer_order M -> type_check_order N -> min_type_infer_order {{{ M N }}}
  | mti_vlookup : forall {x}, min_type_infer_order {{{ #x }}}
  with min_level_infer_order : exp -> Prop :=
  | mlv_typ : forall {i}, min_level_infer_order {{{ Type@i }}}
  | mlv_nat : min_level_infer_order {{{ ℕ }}}
  | mlv_zero : min_level_infer_order {{{ zero }}}
  | mlv_succ : forall {M}, min_level_infer_order {{{ succ M }}}
  | mlv_natrec : forall {A MZ MS M}, min_type_infer_order {{{ rec M return A | zero -> MZ | succ -> MS end }}} -> min_level_infer_order {{{ rec M return A | zero -> MZ | succ -> MS end }}}
  | mlv_pi : forall {A B}, min_level_infer_order A -> min_level_infer_order B -> min_level_infer_order {{{ Π A B }}}
  | mlv_fn : forall {A M}, min_level_infer_order {{{ λ A M }}}
  | mlv_app : forall {M N}, min_level_infer_order M -> min_level_infer_order N -> min_level_infer_order {{{ M N }}}
  | mlv_vlookup : forall {x}, min_type_infer_order {{{ #x }}} -> min_level_infer_order {{{ #x }}}
  .

  #[local]
  Ltac impl_obl_tac :=
    destruct_conjs;
    match goal with
    | |- {{ ⊢ ~_ }} => gen_presups; mautosolve 4
    | H: {{ ~?G ⊢ ~?A : Type@?i }} |- {{ ~?G ⊢ ~?A : Type@(Nat.max ?i ?j) }} => apply lift_exp_max_left; mautosolve 4
    | H: {{ ~?G ⊢ ~?A : Type@?j }} |- {{ ~?G ⊢ ~?A : Type@(Nat.max ?i ?j) }} => apply lift_exp_max_right; mautosolve 4
    | |- {{ ~_ ⊢ ~_ : ~_ }} => gen_presups; mautosolve 4
    | |- type_check_order _ => progressive_inversion; eassumption
    | |- min_type_infer_order _ => progressive_inversion; eassumption
    | |- min_level_infer_order _ => progressive_inversion; eassumption
    | _ => show_hyps; show_goal
    end.

  Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

  #[tactic="impl_obl_tac"]
  Equations type_check G i A (HA : {{ G ⊢ A : Type@i }}) M (H : type_check_order M) : { {{ G ⊢ M : A }} } + { ~ {{ G ⊢ M : A }} } by struct H :=
  | G, i, A, HA, M, H with M => {
    | {{{ Type@j }}} =>
        let*o->b (exist _ k _) := min_level_infer G {{{ Type@j }}} _ while _ in
        let*b _ := typ_subsumption_dec G (max i (S k)) {{{ Type@k }}} _ A _ while _ in
        pureb _
    | {{{ ℕ }}} =>
        let*o->b (exist _ j _) := min_level_infer G {{{ ℕ }}} _ while _ in
        let*b _ := typ_subsumption_dec G (max i (S j)) {{{ Type@j }}} _ A _ while _ in
        pureb _
    | {{{ zero }}} =>
        let*b _ := typ_subsumption_dec G i {{{ ℕ }}} _ A HA while _ in
        pureb _
    | {{{ succ M' }}} =>
        let*b _ := typ_subsumption_dec G i {{{ ℕ }}} _ A HA while _ in
        let*b _ := type_check G 0 {{{ ℕ }}} _ M' _ while _ in
        pureb _
    | {{{ rec M' return A' | zero -> MZ | succ -> MS end }}} =>
        let*o->b (exist _ A''j _) := min_type_infer G _ {{{ rec M' return A' | zero -> MZ | succ -> MS end }}} _ while _ in
        let*b _ := typ_subsumption_dec G (max i (snd A''j)) (fst A''j) _ A _ while _ in
        pureb _
    | {{{ Π B' C' }}} =>
        let*o->b (exist _ j _) := min_level_infer G {{{ Π B' C' }}} _ while _ in
        let*b _ := typ_subsumption_dec G (max i (S j)) {{{ Type@j }}} _ A _ while _ in
        pureb _
    | {{{ λ B' M' }}} with pi_conversion G i A HA => {
      | inleft (exist _ BC _) with inspect BC => {
        | exist _ (B, C) _ =>
            let*o->b (exist _ j _) := min_level_infer G {{{ B' }}} _ while _ in
            let*b _ := conversion_dec G {{{ Type@(max i j) }}} B' _ B _ while _ in
            let*b _ := type_check {{{ G, B' }}} i C _ M' _ while _ in
            pureb _
        }
      | inright _ => right _
      }
    | {{{ M' N' }}} with min_type_infer G _ M' _ => {
      | inleft (exist _ C'j _) with inspect C'j => {
        | exist _ (C', j) _ with pi_conversion G j C' _ => {
          | inleft (exist _ B'A' _) with inspect B'A' => {
            | exist _ (B', A') _ =>
                let*b _ := type_check G j B' _ N' _ while _ in
                let*b _ := typ_subsumption_dec G (max i j) A' _ A _ while _ in
                pureb _
            }
          | inright _ => right _
          }
        }
      | inright HnotM' => _
      }
    | {{{ #x }}} =>
        let*o->b (exist _ A'j _) := min_type_infer G _ {{{ #x }}} _ while _ in
        let*b _ := typ_subsumption_dec G (max i (snd A'j)) (fst A'j) _ A _ while _ in
        pureb _
    | _ =>
        match (_ : False) with
        end
    }
  with min_type_infer G (HG : {{ ⊢ G }}) M (H : min_type_infer_order M) : { '(pair A i) | {{ G ⊢ M : A }} /\ {{ G ⊢ A : Type@i }} /\ (forall A', {{ G ⊢ M : A' }} -> {{ G ⊢ A ⊆ A' }}) } + { forall A, ~ {{ G ⊢ M : A }} } by struct H :=
  | G, HG, M, H with M => {
    | {{{ Type@j }}} =>
        let*o (exist _ i _) := min_level_infer G {{{ Type@j }}} _ while _ in
        pureo (exist _ ({{{ Type@i }}}, S i) _)
    | {{{ ℕ }}} => 
        let*o (exist _ i _) := min_level_infer G {{{ ℕ }}} _ while _ in
        pureo (exist _ ({{{ Type@i }}}, S i) _)
    | {{{ rec M' return A' | zero -> MZ | succ -> MS end }}} =>
        let*b->o _ := type_check G 0 {{{ ℕ }}} _ M' _ while _ in
        let*o (exist _ j _) := min_level_infer {{{ G, ℕ }}} A' _ while _ in
        let*b->o _ := type_check G j {{{ A'[Id,,zero] }}} _ MZ _ while _ in
        let*b->o _ := type_check {{{ G, ℕ, A' }}} j {{{ A'[Wk∘Wk,,succ #1] }}} _ MS _ while _ in
        pureo (exist _ ({{{ A'[Id,,M'] }}}, S j) _)
    | {{{ Π B C }}} =>
        let*o (exist _ i _) := min_level_infer G B _ while _ in
        let*o (exist _ j _) := min_level_infer {{{ G, B }}} C _ while _ in
        let k := max i j in
        pureo (exist _ ({{{ Type@k }}}, S k) _)
    | {{{ λ A' M' }}} =>
        let*o (exist _ j _) := min_level_infer G A' _ while _ in
        let*o (exist _ B'k _) := min_type_infer {{{ G, A' }}} _ M' _ while _ in
        pureo (exist _ ({{{ Π A' ~(fst B'k) }}}, max j (snd B'k)) _)
    | {{{ #x }}} =>
        let*o (exist _ A _) := lookup G _ x while _ in
        let*o (exist _ i _) := min_level_infer G A _ while _ in
        pureo (exist _ (A, i) _)
    | _ =>
        match (_ : False) with
        end
    }
  with min_level_infer G A (H : min_level_infer_order A) : { i | {{ G ⊢ A : Type@i }} /\ (forall j, {{ G ⊢ A : Type@j }} -> i <= j) } + { forall i, ~ {{ G ⊢ A : Type@i }} } by struct H :=
  | G, A, H with A => {
    | {{{ Type@j }}} => pureo (exist _ (S j) _)
    | {{{ ℕ }}} => pureo (exist _ 0 _)
    | {{{ Π B C }}} =>
        let*o (exist _ i _) := min_level_infer G B _ while _ in
        let*o (exist _ j _) := min_level_infer {{{ G, B }}} C _ while _ in
        pureo (exist _ (max i j) _)
    | _ =>
        match (_ : False) with
        end
    }
  .

  Next Obligation with mautosolve.
    enough {{ G ⊢ ℕ ⊆ A }} by contradiction.
    eauto using wf_zero_inversion.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ ℕ ⊆ A }} by contradiction.
    eapply wf_succ_inversion; eauto.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ M' : ℕ }} by contradiction.
    eapply wf_succ_inversion'...
  Qed.

  Next Obligation with mautosolve.
    intuition.
  Qed.

  Lemma vlookup_uniqueness : forall {Γ x A A'},
      {{ #x : A ∈ Γ }} ->
      {{ #x : A' ∈ Γ }} ->
      A = A'.
  Proof.
    intros * HA.
    dependent induction HA generalizing A'; inversion_clear 1; eauto.
    erewrite IHHA; eauto.
  Qed.

  Next Obligation with mautosolve.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ ℕ : Type@0 }} by intuition.
    mauto.
  Qed.

  Next Obligation with mautosolve.
    mauto 4 using lift_exp_max_right.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ Type@j ⊆ A }} by contradiction.
    assert {{ G ⊢ Type@0 ⊆ A }} by (apply wf_nat_inversion; mauto).
    assert (exists l k, 0 <= k /\ {{ G ⊢ A ≈ Type@k : Type@l }}) as [? [k []]] by eauto using typ_subsumption_left_typ.
    assert (j <= k) by mauto.
    assert {{ G ⊢ Type@j ⊆ Type@k }} by mauto 4.
    mauto 4.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ Type@j : Type@(S j) }} by intuition.
    mauto 4.
  Qed.

  Next Obligation with mautosolve.
    mauto 4 using lift_exp_max_right.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ Type@k ⊆ A }} by contradiction.
    assert {{ G ⊢ Type@(S j) ⊆ A }} by (apply wf_typ_inversion; mauto).
    assert (k <= (S j)) by mauto.
    assert {{ G ⊢ Type@k ⊆ Type@(S j) }} by mauto 4.
    mauto 4.
  Qed.

  Next Obligation with mautosolve.
    intuition.
  Qed.

  Next Obligation with mautosolve.
  Qed.

  Next Obligation with mautosolve.
    enough (exists i, {{ G ⊢ B' : Type@i }}) as [] by firstorder.
    assert (exists C', {{ G, B' ⊢ M' : C' }} /\ {{ G ⊢ Π B' C' ⊆ A }}) as [? []] by mauto using wf_fn_inversion...
  Qed.

  Next Obligation with mautosolve.
    gen_presups.
    assert {{ G ⊢ B : Type@i }} by (eapply wf_pi_inversion'; eauto).
    impl_obl_tac.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ B' ≈ B : Type @ (Nat.max i j) }} by firstorder.
    assert (exists C', {{ G, B' ⊢ M' : C' }} /\ {{ G ⊢ Π B' C' ⊆ A }}) as [C' []] by mauto using wf_fn_inversion.
    TODOtac "Pi equivalence is invertible".
  Qed.

  Next Obligation with mautosolve.
    gen_presups.
    assert {{ ⊢ G, B' ≈ G, B }} by mauto 3.
    enough {{ G, B ⊢ C : Type@i }} by mauto 3.
    eapply wf_pi_inversion'; eauto.
  Qed.

  Next Obligation with mautosolve.
    assert (exists C', {{ G, B' ⊢ M' : C' }} /\ {{ G ⊢ Π B' C' ⊆ A }}) as [C' []] by mauto using wf_fn_inversion.
    TODOtac "Pi equivalence is invertible".
  Qed.

  Next Obligation with mautosolve.
    gen_presups.
    assert {{ G ⊢ Π B C : Type@i }} by (gen_presups; eauto).
    assert {{ G, B ⊢ C : Type@i }} by (eapply wf_pi_inversion'; mauto 3).
    assert {{ ⊢ G, B' ≈ G, B }} by mauto 3.
    assert {{ G, B' ⊢ C : Type@i }} by mauto 3.
    enough {{ G ⊢ Π B' C ≈ Π B C : Type@(max i j) }} by mauto.
    econstructor; mauto 3.
    enough {{ G, B' ⊢ C : Type@(max i j) }} by mauto 3.
    impl_obl_tac.
  Qed.

  Next Obligation with mautosolve.
    assert (exists C', {{ G, B' ⊢ M' : C' }} /\ exists j, {{ G ⊢ Π B' C' ≈ A : Type@j }}) as [C' [? []]] by mauto using wf_fn_inversion'.
    firstorder.
  Qed.

  Next Obligation with mautosolve.
  Qed.

  Next Obligation with mautosolve.
    gen_presups.
    eapply wf_pi_inversion'; eauto.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ N' : B' }} by contradiction.
    assert (exists B' A' : typ, {{ G ⊢ M' : Π B' A' }} /\ {{ G ⊢ N' : B' }} /\ {{ G ⊢ ~ (a_sub A' {{{ Id,, N' }}}) ⊆ A }}) as [B'' [A'']] by mauto.
    destruct_conjs.
    gen_presups.
    eapply wf_pi_inversion'; eauto.
  Qed.

  Next Obligation with mautosolve.
    assert {{ G ⊢s Id,,M' : G, ℕ }} by mauto.
    mauto using lift_exp_max_right.
  Qed.

  Next Obligation with mautosolve.
    mauto using lift_exp_max_left.
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ A'[Id,,M'] ⊆ A }} by contradiction.
    eapply wf_natrec_inversion...
  Qed.

  Next Obligation with mautosolve.
    enough {{ G ⊢ MZ : A'[Id,,zero] }} by contradiction.
    eapply wf_natrec_inversion...
  Qed.

  Next Obligation with mautosolve.
    enough {{ G, ℕ, A' ⊢ MS : A'[Wk∘Wk,,succ #1] }} by contradiction.
    eapply wf_natrec_inversion...
  Qed.

  Next Obligation with mautosolve.
    apply lift_exp_max_right...
  Qed.

  Next Obligation with mautosolve.
    apply lift_exp_max_left...
  Qed.

  Next Obligation with mautosolve.
    apply lift_exp_max_right...
  Qed.

  Next Obligation with mautosolve.
    apply lift_exp_max_left...
  Qed.

  Next Obligation with mautosolve.
    enough (exists i, {{ G ⊢ A' : Type@i }}) as [] by firstorder.
    assert (exists i B', {{ G ⊢ A' : Type@i }} /\ {{ G, A' ⊢ B' : Type@i }} /\ {{ G, A' ⊢ M' : B' }} /\ {{ G ⊢ Π A' B' ≈ A : Type@i }}) by mauto using wf_fn_inversion.
    destruct_conjs...
  Qed.

  Next Obligation with mautosolve.
    enough (exists B', {{ G, A' ⊢ M' : B' }}) as [] by firstorder.
    assert (exists i B', {{ G ⊢ A' : Type@i }} /\ {{ G, A' ⊢ B' : Type@i }} /\ {{ G, A' ⊢ M' : B' }} /\ {{ G ⊢ Π A' B' ≈ A : Type@i }}) by mauto using wf_fn_inversion.
    destruct_conjs...
  Qed.

  Next Obligation with mautosolve.
    rename e into B'.
    apply lift_exp_max_right...
  Qed.

  Next Obligation with mautosolve.
    apply lift_exp_max_left...
  Qed.

  Next Obligation with mautosolve.
    (* This case is not true! The implementation for lambda should be fixed. *)
    rename e into B'.
    enough {{ G ⊢ Π A' B' ⊆ A }} by contradiction.
    assert (exists i B', {{ G ⊢ A' : Type@i }} /\ {{ G, A' ⊢ B' : Type@i }} /\ {{ G, A' ⊢ M' : B' }} /\ {{ G ⊢ Π A' B' ≈ A : Type@i }}) by mauto using wf_fn_inversion.
    destruct_conjs.
  Abort.

  (* Next Obligation. mauto. Qed. *)
  (* Next Obligation. mauto. Qed. *)

  (* Next Obligation with mautosolve. *)
  (*   enough {{ G ⊢ B : Type@i }} by firstorder. *)
  (*   eapply wf_pi_inversion'... *)
  (* Qed. *)

  (* Next Obligation with mautosolve. *)
  (*   enough {{ G, B ⊢ C : Type@i0 }} by firstorder. *)
  (*   eapply wf_pi_inversion'... *)
  (* Qed. *)

  (* Next Obligation. mauto. Qed. *)
End type_check.
