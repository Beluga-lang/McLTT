From Coq Require Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString ExtrOcamlZInt.

From Equations Require Import Equations.

From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base Completeness Soundness.
From Mcltt.Core.Syntactic Require Import SystemOpt.
From Mcltt.Extraction Require Import NbE TypeCheck.
From Mcltt.Frontend Require Import Elaborator Parser.
Import MenhirLibParser.Inter.
Import Syntax_Notations.

Variant main_result :=
  | AllGood : forall cst_typ cst_exp A M W,
      elaborate cst_typ nil = Some A ->
      elaborate cst_exp nil = Some M ->
      {{ ⋅ ⊢ M : A }} ->
      nbe {{{ ⋅ }}} M A W ->
      main_result
  | TypeCheckingFailure : forall A M, ~ {{ ⋅ ⊢ M : A }} -> main_result
  | ElaborationFailure : forall cst, elaborate cst nil = None -> main_result
  | ParserFailure : Aut.state -> Aut.Gram.token -> main_result
  | ParserTimeout : nat -> main_result
.

Definition inspect {A} (x : A) : { y | x = y } := exist _ x eq_refl.
Extraction Inline inspect.

#[local]
Ltac impl_obl_tac := try eassumption.
#[tactic="impl_obl_tac"]
Equations main (log_fuel : nat) (buf : buffer) : main_result :=
| log_fuel, buf with Parser.prog log_fuel buf => {
  | Parsed_pr (cst_exp, cst_typ) _ with inspect (elaborate cst_typ nil) => {
    | exist _ (Some A) _ with inspect (elaborate cst_exp nil) => {
      | exist _ (Some M) _ with type_check_closed A _ M _ => {
        | left  _ with nbe_impl {{{ ⋅ }}} M A _ => {
          | exist _ W _ => AllGood cst_typ cst_exp A M W _ _ _ _
          }
        | right _ => TypeCheckingFailure A M _
        }
      | exist _ None     _ => ElaborationFailure cst_exp _
      }
    | exist _ None     _ => ElaborationFailure cst_typ _
    }
  | Fail_pr_full s t               => ParserFailure s t
  | Timeout_pr                     => ParserTimeout log_fuel
  }
.
Next Obligation.
  eapply elaborator_gives_user_exp; eassumption.
Qed.
Next Obligation.
  eapply elaborator_gives_user_exp; eassumption.
Qed.
Next Obligation.
  (on_all_hyp: fun H => apply soundness in H as [? []]).
  eapply nbe_order_sound.
  eassumption.
Qed.

Extraction Language OCaml.

Set Extraction Flag 1007.
Set Extraction Output Directory "../driver/extracted".
