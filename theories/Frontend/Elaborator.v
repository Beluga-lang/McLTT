From Coq Require Import Lia List MSets PeanoNat String FunInd.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax.

Open Scope string_scope.

Module StrSet := Make String_as_OT.
Module StrSProp := MSetProperties.Properties StrSet.

(** One cannot import notation from module type without
    restricting a module to that exact type.
    Thus, here we repeat the notation from [WSetsOn]. *)
Notation "s [<=] t" := (StrSet.Subset s t) (at level 70, no associativity).

(** De-monadify with pattern matching for now *)
Fixpoint lookup (s : string) (ctx : list string) : option nat :=
  match ctx with
  | nil => None
  | c::cs =>
      if string_dec c s
      then Some 0
      else
        match lookup s cs with
        | Some n => Some (n + 1)%nat
        | None => None
        end
  end
.

Fixpoint elaborate (cst : Cst.obj) (ctx : list string) : option exp :=
  match cst with
  | Cst.typ n => Some (a_typ n)
  | Cst.nat => Some a_nat
  | Cst.zero => Some a_zero
  | Cst.succ c =>
      match elaborate c ctx with
      | Some a => Some (a_succ a)
      | None => None
      end
  | Cst.natrec n mx m z sx sr s =>
      match elaborate m (mx :: ctx), elaborate z ctx, elaborate s (sr :: sx :: ctx), elaborate n ctx with
      | Some m, Some z, Some s, Some n => Some (a_natrec m z s n)
      | _, _, _, _ => None
      end
  | Cst.var s =>
      match lookup s ctx with
      | Some n => Some (a_var n)
      | None => None
      end
  | Cst.fn s t c =>
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_fn t a)
      | _, _ => None
      end
  | Cst.app c1 c2 =>
      match elaborate c1 ctx, elaborate c2 ctx with
      | None, _ => None
      | _, None => None
      | Some a1, Some a2 => Some (a_app a1 a2)
      end
  | Cst.pi s t c =>
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_pi t a)
      | _, _ => None
      end
  end
.

Functional Scheme elaborate_fun_ind := Induction for elaborate Sort Prop.

Generalizable All Variables.

Inductive user_exp : exp -> Prop :=
| user_exp_typ :
  `( user_exp (a_typ i) )
| user_exp_nat :
  `( user_exp a_nat )
| user_exp_zero :
  `( user_exp a_zero )
| user_exp_succ :
  `( user_exp M ->
     user_exp (a_succ M) )
| user_exp_natrec :
  `( user_exp A ->
     user_exp MZ ->
     user_exp MS ->
     user_exp M ->
     user_exp (a_natrec A MZ MS M) )
| user_exp_pi :
  `( user_exp A ->
     user_exp B ->
     user_exp (a_pi A B) )
| user_exp_fn :
  `( user_exp A ->
     user_exp M ->
     user_exp (a_fn A M) )
| user_exp_app :
  `( user_exp M ->
     user_exp N ->
     user_exp (a_app M N) )
| user_exp_vlookup :
  `( user_exp (a_var x) ).

#[export]
Hint Constructors user_exp : mctt.

Lemma user_exp_nf : forall M, user_exp (nf_to_exp M)
with user_exp_ne : forall M, user_exp (ne_to_exp M).
Proof.
  - clear user_exp_nf; induction M; mauto 3.
  - clear user_exp_ne; induction M; mauto 3.
Qed.

Lemma elaborator_gives_user_exp : forall O vs M,
    elaborate O vs = Some M ->
    user_exp M.
Proof.
  intros * Heq. gen M.
  functional induction (elaborate O vs) using elaborate_fun_ind;
    intros; inversion_clear Heq; mauto 4.

  econstructor; mauto 3.
Qed.

Fixpoint cst_variables (cst : Cst.obj) : StrSet.t :=
 match cst with
  | Cst.typ n => StrSet.empty
  | Cst.nat => StrSet.empty
  | Cst.zero => StrSet.empty
  | Cst.succ c => cst_variables c
  | Cst.natrec n mx m z sx sy s => StrSet.union (StrSet.union (cst_variables n) (StrSet.remove mx (cst_variables m))) (StrSet.union (cst_variables z) (StrSet.remove sx (StrSet.remove sy (cst_variables s))))
  | Cst.var s => StrSet.singleton s
  | Cst.fn s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.pi s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.app c1 c2 => StrSet.union (cst_variables c1) (cst_variables c2)
 end
.

Inductive closed_at : exp -> nat -> Prop :=
 | ca_var : forall x n, x < n -> closed_at (a_var x) n
 | ca_lam : forall t b n, closed_at t n -> closed_at b (1+n) -> closed_at (a_fn t b) n
 | ca_pi : forall t b n, closed_at t n -> closed_at b (1+n) -> closed_at (a_pi t b) n
 | ca_app : forall a1 a2 n, closed_at a1 n -> closed_at a2 n ->
            closed_at (a_app a1 a2) n
 | ca_nat : forall n, closed_at (a_nat) n
 | ca_zero : forall n, closed_at (a_zero) n
 | ca_type : forall n m, closed_at (a_typ m) n
 | ca_succ : forall a n, closed_at a n -> closed_at (a_succ a) n
 | ca_natrec : forall n m z s l, closed_at n l -> closed_at m (1+l) -> closed_at z l -> closed_at s (2+l) -> closed_at (a_natrec m z s n) l
.
#[local]
Hint Constructors closed_at: mctt.

(** Lemma for the well_scoped proof, lookup succeeds if var is in context *)
Lemma lookup_known (s : string) (ctx : list string) (H_in : List.In s ctx) : exists n : nat, (lookup s ctx = Some n /\ n < List.length ctx).
Proof.
  induction ctx as [| c ctx' IHctx]; simpl in *.
  - contradiction.
  - destruct (string_dec c s); subst.
    + eexists; split; auto. lia.
    + destruct H_in; try contradiction.
      destruct IHctx as [? [? ?]]; [assumption |].
      rewrite H0.
      eexists; split; auto. lia.
Qed.

(** Lemma for the well_scoped proof, lookup result always less than context length *)
Lemma lookup_bound s : forall ctx m, lookup s ctx = Some m -> m < (List.length ctx).
  induction ctx.
  - intros. discriminate H.
  - intros. destruct (string_dec a s).
    + rewrite e in H.
      simpl in H.
      destruct string_dec in H.
      * inversion H.
        unfold Datatypes.length.
        apply (Nat.lt_0_succ).
      * contradiction n. reflexivity.
    + simpl in H.
      destruct string_dec in H.
      * contradiction n.
      * destruct (lookup s ctx);
          try discriminate.
        inversion H.
        rewrite H1.
        simpl.
        pose (IHctx (m-1)).
        rewrite <- H1 in l.
        rewrite (Nat.add_sub n1 1) in l.
        rewrite <- H1.
        specialize (l eq_refl).
        lia.
Qed.

Import StrSProp.Dec.

Lemma Subset_to_In : forall xs x, StrSet.singleton x [<=] StrSProp.of_list xs -> In x xs.
Proof.
  intro xs; induction xs; simpl; intros.
  - rewrite <- F.empty_iff.
    apply (H x).
    fsetdec.
  - specialize (H x).
    rewrite F.add_iff in H.
    destruct H; [fsetdec | auto |].
    right. eapply IHxs.
    intros y Hy.
    assert (y = x); fsetdec.
Qed.

(** *** Well scopedness lemma *)

(** If the set of free variables in a cst are contained in a context
    then elaboration succeeds with that context, and the result is a closed term *)
Lemma well_scoped (cst : Cst.obj) : forall ctx,  cst_variables cst [<=] StrSProp.of_list ctx  ->
exists a : exp, (elaborate cst ctx = Some a) /\ (closed_at a (List.length ctx)).
Proof.
  induction cst; intros; simpl in *; mauto.
  - (* succ *)
    destruct (IHcst _ H) as [ast [-> ?]]; mauto.
  - (* natrec *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    assert (cst_variables cst3 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst4 [<=] StrSProp.of_list (s1 :: s0 :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]];
      destruct (IHcst3 _ H2) as [ast'' [-> ?]];
      destruct (IHcst4 _ H3) as [ast''' [-> ?]]; mauto.
  - (* pi *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - (* fn *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - (* app *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list ctx) by fsetdec.
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - apply Subset_to_In in H.
    edestruct lookup_known as [? [-> ?]]; [auto |].
    apply (In_nth _ _ s)  in H.
    destruct H as [? [? ?]].
    mauto.
Qed.

Example test_elab : elaborate Cst.nat nil = Some a_nat.
Proof. reflexivity. Qed.

Example test_elab2 : elaborate (Cst.fn "s" Cst.nat (Cst.fn "x" Cst.nat (Cst.fn "s" Cst.nat (Cst.var "q")))) nil = None.
Proof. reflexivity. Qed.
