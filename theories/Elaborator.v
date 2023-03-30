Require Export String.
Require Export List.
Require Export Coq.Structures.OrderedTypeEx.
Require Export MSets MSetInterface MSetFacts MSetProperties.
Require Export Coq.Lists.SetoidList.
Require Export Arith.
From Mcltt Require Import Syntax.


Open Scope string_scope.

Definition cst_term := Syntax.Cst.obj.
Definition ast_term := Syntax.exp.

Module StrSet := Make String_as_OT.
Module StrSProp := MSetProperties.Properties StrSet.

(*Copied from the MSetsInterface file because I couldn't figure out how to import it*)
Notation "s  [<=]  t" := (StrSet.Subset s t) (at level 70, no associativity).



(**De-monadify with pattern matching for now**)
Fixpoint lookup (s : string) (ctx : list string) : (option nat) :=
 match ctx with
  | nil => None
  | c::cs => if string_dec c s then (Some 0) else 
                  match lookup s cs  with
                        | Some n => Some (n + 1)
                        | None => None
                  end
 end
.

Check Cst.typ.




Fixpoint elaborate (cst : cst_term) (ctx : list string) : (option ast_term) :=
 match cst with 
 | Cst.typ n => Some (a_typ n)
 | Cst.nat => Some a_nat
 | Cst.zero => Some a_zero
 | Cst.succ c => match elaborate c ctx with
              | Some a => Some (a_succ a)
              | None => None
              end
 | Cst.var s =>  match lookup s ctx with
              | Some n => Some (a_var n)
              | None => None
              end
 | Cst.fn s t c => match elaborate c (s::ctx), elaborate t ctx with
              | Some a, Some t => Some (a_fn t a)
              | _, _ => None
              end 
 | Cst.app c1 c2 => match elaborate c1 ctx, elaborate c2 ctx with
              | None, _ => None
              | _, None => None
              | Some a1, Some a2 => Some (a_app a1 a2)
              end 
 | Cst.pi s t c => match elaborate c (s::ctx), elaborate t ctx with
              | Some a, Some t => Some (a_pi t a)
              | _,_ => None
              end
 end
.

Fixpoint cst_variables (cst : cst_term) : StrSet.t :=
 match cst with
  | Cst.typ n => StrSet.empty
  | Cst.nat => StrSet.empty
  | Cst.zero => StrSet.empty
  | Cst.succ c => cst_variables c
  | Cst.var s => StrSet.singleton s
  | Cst.fn s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.pi s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
  | Cst.app c1 c2 => StrSet.union (cst_variables c1) (cst_variables c2)
 end
.

Inductive closed_at : ast_term -> nat -> Prop :=
 | ca_var : forall x n, x < n -> closed_at (a_var x) n
 | ca_lam : forall t b n, closed_at t n -> closed_at b (1+n) -> closed_at (a_fn t b) n
 | ca_pi : forall t b n, closed_at t n -> closed_at b (1+n) -> closed_at (a_pi t b) n
 | ca_app : forall a1 a2 n m, closed_at a1 n -> closed_at a2 m -> 
            closed_at (a_app a1 a2) (max n m)
 | ca_nat : forall n, closed_at (a_nat) n
 | ca_zero : forall n, closed_at (a_zero) n
 | ca_type : forall n m, closed_at (a_typ m) n
 | ca_succ : forall a n, closed_at a n -> closed_at (a_succ a) n 
.

(*Lemma for the well_scoped proof, lookup succeeds if var is in context*)
Lemma lookup_known (s : string) (ctx : list string) (H_in : List.In s ctx) : exists n : nat, (lookup s ctx = Some n).
Proof.
  induction ctx as [| c ctx' IHctx].
  - simpl.
    contradiction.
  - simpl.
    destruct (string_dec c s).
    subst.
    eauto.
    assert (In s ctx').
    {
      destruct (in_inv H_in).
      * contradiction n. 
      * exact H.
    } 
    destruct (IHctx H).
    rewrite H0.
    eauto.    
Qed.
(*Lemma for the well_scoped proof, lookup result always less than context length*)
Lemma lookup_bound s : forall ctx m, lookup s ctx = Some m -> m < (length ctx).
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
      * destruct (lookup s ctx).
        --inversion H.
          rewrite H1.
          simpl.
          pose (IHctx (m-1)).
          rewrite <- H1 in l.
          rewrite (Nat.add_sub n1 1) in l.
          rewrite <- H1.
          rewrite Nat.add_1_r.
          apply (Arith_prebase.lt_n_S_stt (n1) (length ctx)).
          apply l.
          reflexivity.
        --discriminate H.
Qed.

(*Well scopedness lemma: If the set of free variables in a cst are contained in a context
  then elaboration succeeds with that context, and the result is a closed term*)
Lemma well_scoped (cst : cst_term) : forall ctx,  cst_variables cst [<=] StrSProp.of_list ctx  ->
exists a : ast_term, (elaborate cst ctx = Some a) /\ (closed_at a (length ctx)).
Proof.
  induction cst.
  - intros.
    exists (a_typ n).
    split.
    + reflexivity.
    + exact (ca_type (length ctx) n).

  - intros.
    exists (a_nat).
    split.
    + reflexivity.
    + exact (ca_nat (length ctx)).

  - intros.
    exists (a_zero).
    split.
    + reflexivity.
    + exact (ca_zero (length ctx)).

  - intros.
    destruct ((IHcst ctx) H).
    destruct H0.
    exists (a_succ x).
    split.
    + simpl. rewrite H0. reflexivity.
    + exact (ca_succ x (length ctx) H1).
  - intros.
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx).
    {
      unfold "[<=]" in H |- *.
      intros.
      apply (H a).
      apply StrSet.union_spec.
      left.
      exact H0.
    }
    assert (cst_variables cst2 [<=] StrSProp.of_list ctx).
    {
      unfold "[<=]" in H |- *.
      intros.
      apply (H a).
      apply StrSet.union_spec.
      right.
      exact H1.
    }
    destruct ((IHcst1 ctx) H0).
    destruct H2.
    destruct ((IHcst2 ctx) H1).
    destruct H4.
    exists (a_app x x0).
    split.
    + simpl.
      rewrite H2.
      rewrite H4.
      reflexivity.
    + assert (S := ca_app x x0 (length ctx) (length ctx) H3 H5).
      rewrite -> (Nat.max_id (length ctx)) in S.
      exact S.
  - intros.
    simpl in H.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s::ctx)).
    {
      simpl.
      unfold "[<=]" in H |- *.
      intros.
      destruct (string_dec a s).
      - rewrite e.
        apply StrSet.add_spec.
        left.
        reflexivity.
      - apply StrSet.add_spec.
        right.
        apply H.
        apply StrSet.union_spec.
        right.
        apply StrSet.remove_spec.
        split.
        + exact H0.
        + exact n.
    }
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx).
    {
      simpl.
      unfold "[<=]" in H |- *.
      intros.
      apply H.
      apply StrSet.union_spec.
      left.
      exact H1.
    }
    destruct ((IHcst2 (s::ctx)) H0).
    destruct H2.
    destruct (IHcst1 ctx H1).
    destruct H4.
    simpl.
    rewrite -> H2.
    rewrite -> H4.
    exists (a_fn x0 x).
    split.
    + reflexivity.
    + exact (ca_lam x0 x (length ctx) H5 H3).

  - intros.
    simpl in H.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s::ctx)).
    {
      simpl.
      unfold "[<=]" in H |- *.
      intros.
      destruct (string_dec a s).
      - rewrite e.
        apply StrSet.add_spec.
        left.
        reflexivity.
      - apply StrSet.add_spec.
        right.
        apply H.
        apply StrSet.union_spec.
        right.
        apply StrSet.remove_spec.
        split.
        + exact H0.
        + exact n.
    }
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx).
    {
      simpl.
      unfold "[<=]" in H |- *.
      intros.
      apply H.
      apply StrSet.union_spec.
      left.
      exact H1.
    }
    destruct ((IHcst2 (s::ctx)) H0).
    destruct H2.
    destruct (IHcst1 ctx H1).
    destruct H4.
    simpl.
    rewrite -> H2.
    rewrite -> H4.
    exists (a_pi x0 x).
    split.
    + reflexivity.
    + exact (ca_pi x0 x (length ctx) H5 H3).

    

  - intros.
    simpl in *.
    assert (In s ctx).
    {
      unfold "[<=]" in H.
      assert (I := H s).
      apply StrSProp.of_list_1 in I.
      apply InA_alt in I.
      destruct I.
      destruct H0.
      rewrite <- H0 in H1.
      exact H1.
      apply StrSet.singleton_spec.
      reflexivity.
    }
    destruct (lookup_known s ctx H0).
    rewrite H1.
    exists (a_var x).
    split.
    + reflexivity.
    + exact (ca_var x (length ctx) (lookup_bound s ctx x H1)).
Qed.



Check elaborate Cst.nat nil : option ast_term.
Fail Check elaborate (Cst.succ a_nat) : option ast_term.


Compute (elaborate (Cst.fn "s" (Cst.typ 5) (Cst.var "s")) nil).
Compute (elaborate (Cst.fn "s" (Cst.typ 0) (Cst.fn "x" Cst.nat (Cst.app (Cst.var "x") (Cst.var "s")))) nil).
Compute (elaborate (Cst.fn "s" Cst.nat (Cst.fn "x" Cst.nat (Cst.fn "s" Cst.nat (Cst.var "s")))) nil).
Compute (elaborate (Cst.fn "s" (Cst.typ 10) (Cst.fn "x" (Cst.typ 0) (Cst.fn "s" (Cst.typ 5) (Cst.var "q")))) nil).


Example test_elab : elaborate Cst.nat nil = Some a_nat.
Proof. reflexivity. Qed.

Example test_elab2 : elaborate (Cst.fn "s" Cst.nat (Cst.fn "x" Cst.nat (Cst.fn "s" Cst.nat (Cst.var "q")))) nil = None.
Proof. reflexivity. Qed.




