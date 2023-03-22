Require Export String.
Require Export List.
Require Export Coq.Structures.OrderedTypeEx.
Require Export MSets MSetInterface MSetFacts MSetProperties.
Require Export Coq.Lists.SetoidList.
Require Export Arith.

Open Scope string_scope.


Module StrSet := Make String_as_OT.
Module StrSProp := MSetProperties.Properties StrSet.

(*Copied from the MSetsInterface file because I couldn't figure out how to import it*)
Notation "s  [<=]  t" := (StrSet.Subset s t) (at level 70, no associativity).


Inductive cst_term : Set :=
 | cType (level : nat)
 | cNat
 | cVar (s : string)
 | cZero
 | cSucc (t : cst_term)
 | cFun (s : string) (t : cst_term)
 | cApp (t1 : cst_term) (t2 : cst_term).

Inductive ast_term : Set :=
 | aType (level : nat)
 | aNat
 | aVar (n : nat)
 | aZero
 | aSucc (t : ast_term)
 | aFun (t : ast_term)
 | aApp (t1 : ast_term) (t2 : ast_term).


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


Fixpoint elaborate (cst : cst_term) (ctx : list string) : (option ast_term) :=
 match cst with 
 | cType n => Some (aType n)
 | cNat => Some aNat
 | cZero => Some aZero
 | cSucc c => match elaborate c ctx with
              | Some a => Some (aSucc a)
              | None => None
              end
 | cVar s =>  match lookup s ctx with
              | Some n => Some (aVar n)
              | None => None
              end
 | cFun s c => match (elaborate c (s::ctx)) with
              | Some a => Some (aFun a)
              | None => None
              end 
 | cApp c1 c2 => match elaborate c1 ctx, elaborate c2 ctx with
              | None, _ => None
              | _, None => None
              | Some a1, Some a2 => Some (aApp a1 a2)
              end 
 end
.

Fixpoint cst_variables (cst : cst_term) : StrSet.t :=
 match cst with
  | cType n => StrSet.empty
  | cNat => StrSet.empty
  | cZero => StrSet.empty
  | cSucc c => cst_variables c
  | cVar s => StrSet.singleton s
  | cFun s c => StrSet.remove s (cst_variables c)
  |cApp c1 c2 => StrSet.union (cst_variables c1) (cst_variables c2)
 end
.

Inductive closed_at : ast_term -> nat -> Prop :=
 | ca_var : forall x n, x < n -> closed_at (aVar x) n
 | ca_lam : forall t n, closed_at t (1+n) -> closed_at (aFun t) n
 | ca_app : forall a1 a2 n m, closed_at a1 n -> closed_at a2 m -> 
            closed_at (aApp a1 a2) (max n m)
 | ca_nat : forall n, closed_at (aNat) n
 | ca_zero : forall n, closed_at (aZero) n
 | ca_type : forall n m, closed_at (aType m) n
 | ca_succ : forall a n, closed_at a n -> closed_at (aSucc a) n 
.

(*Lemma for the well_scoped proof, lookup succeeds if var is in context*)
Lemma lookup_known (s : string) (ctx : list string) (H_in : List.In s ctx) : exists n : nat, (lookup s ctx = Some n).
Proof.
  induction ctx as [| c ctx' IHctx].
  - simpl.
    contradiction.
  - simpl.
    destruct (string_dec s c).
    rewrite e.
    exists 0.
    destruct (string_dec c c).
    + reflexivity.
    + contradiction n. reflexivity.
    + assert (In s ctx').
      destruct (in_inv H_in).
      * contradiction n. symmetry. exact H.
      * exact H.
      * destruct (IHctx H).
        rewrite H0.
        exists (x+1).
        destruct (string_dec c s).
        -- contradiction n. symmetry. exact e.
        -- reflexivity.
Qed.
(*Lemma for the well_scoped proof, lookup result always less than context length*)
Lemma lookup_bound s : forall ctx m, lookup s ctx = Some m -> m < (length ctx).
  induction ctx.
  - intros. discriminate H.
  - intros. destruct (string_dec s a).
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
        symmetry.
        exact e.
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
    exists (aType level).
    split.
    + reflexivity.
    + exact (ca_type (length ctx) level).

  - intros.
    exists (aNat).
    split.
    + reflexivity.
    + exact (ca_nat (length ctx)).

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
    exists (aVar x).
    split.
    + reflexivity.
    + exact (ca_var x (length ctx) (lookup_bound s ctx x H1)).

  - intros.
    exists (aZero).
    split.
    + reflexivity.
    + exact (ca_zero (length ctx)).
  
  - intros.
    destruct ((IHcst ctx) H).
    destruct H0.
    exists (aSucc x).
    split.
    + simpl. rewrite H0. reflexivity.
    + exact (ca_succ x (length ctx) H1).

  - intros.
    simpl in H.
    assert (cst_variables cst [<=] StrSProp.of_list (s::ctx)).
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
        apply StrSet.remove_spec.
        split.
        + exact H0.
        + exact n.
    }
    destruct ((IHcst (s::ctx)) H0).
    destruct H1.
    simpl.
    rewrite -> H1.
    exists (aFun x).
    split.
    + reflexivity.
    + exact (ca_lam x (length ctx) H2).
    
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
    exists (aApp x x0).
    split.
    + simpl.
      rewrite H2.
      rewrite H4.
      reflexivity.
    + assert (S := ca_app x x0 (length ctx) (length ctx) H3 H5).
      rewrite -> (Nat.max_id (length ctx)) in S.
      exact S.
Qed.



Check elaborate cNat nil : option ast_term.
Fail Check elaborate (cSucc aNat) : option ast_term.


Compute (elaborate (cFun "s" (cVar "s")) nil).
Compute (elaborate (cFun "s" (cFun "x" (cApp (cVar "x") (cVar "s")))) nil).
Compute (elaborate (cFun "s" (cFun "x" (cFun "s" (cVar "s")))) nil).
Compute (elaborate (cFun "s" (cFun "x" (cFun "s" (cVar "q")))) nil).


Example test_elab : elaborate cNat nil = Some aNat.
Proof. reflexivity. Qed.

Example test_elab2 : elaborate (cFun "s" (cFun "x" (cFun "s" (cVar "q")))) nil = None.
Proof. reflexivity. Qed.




