Require Export String.
Require Export List.
Require Export Coq.Structures.OrderedTypeEx.
Require Export MSets MSetInterface MSetFacts MSetProperties.
Require Export Coq.Lists.SetoidList.
Require Export Arith.

Open Scope string_scope.


Module StrSet := Make String_as_OT.
Module StrSProp := MSetProperties.Properties StrSet.


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
  | c::cs => if String.eqb c s then (Some 0) else 
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

Fixpoint max_index (ast : ast_term) : option nat :=
  match ast with
    | aType n => None
    | aNat => None
    | aZero => None
    | aSucc a => max_index a
    | aVar n => Some n
    | aFun a => max_index a
    | aApp a1 a2 => match (max_index a1), (max_index a2) with
                    | Some n1, None => Some n1
                    | None, Some n2 => Some n2
                    | Some n1, Some n2 => Some (max n1 n2)
                    | None, None => None
                    end
  end
.

Fixpoint elab_success (cst : cst_term) (ctx : list string) : Prop :=
  match cst with
  | cType n => True
  | cNat => True
  | cZero => True
  | cSucc c => elab_success c ctx
  | cVar s => In s ctx
  | cFun s c => elab_success c (s::ctx)
  | cApp c1 c2 => and (elab_success c1 ctx) (elab_success c2 ctx)
  end
.


Fixpoint closed_at (ast : ast_term) (n : nat) : Prop :=
match ast with
  | aVar m => m < n
  | aFun a => closed_at a n
  | aApp a1 a2 => and (closed_at a1 n) (closed_at a2 n)
  | _ => True
end.


Lemma elab_concat (cst : cst_term) (ctx : list string) (s : string) (x : elab_success cst ctx) : elab_success cst (s::ctx).
Proof.
  induction cst.
  all : simpl ; auto.
  simpl in x.
  
  (*Another situation where I'm stuck and not sure how I can use the induction
    hypothesis that's available. *)

Admitted. 
(*Lemma for the older version of the well_scoped proof, not needed for the inductive predicate version*)
Lemma lookup_known (s : string) (ctx : list string) (p : List.In s ctx) : exists n : nat, (lookup s ctx = Some n).
Proof.
  
  
  induction ctx as [| c ctx' IHctx].
  simpl.
  contradiction.

  
  
  assert (str_dec := String.string_dec s c).
  destruct str_dec.
  
  simpl.
  exists 0.
  assert (eqcs : c =? s = true).
  apply (String.eqb_eq c s).
  symmetry.
  exact e.

  rewrite eqcs.
  simpl.
  reflexivity.
  
  assert (In s ctx').
  assert (H := List.in_inv p).
  destruct H.
  destruct n.
  symmetry.
  exact H.
  exact H.

  assert (I := In_nth ctx' s "" H).
  destruct(I).
  destruct(H0).
  destruct (IHctx H).

  simpl.
  assert (Q : s =? c = false).
  apply eqb_neq.
  exact n.
  rewrite eqb_sym.
  rewrite Q.
  exists(x0 + 1).
  rewrite H3.
  reflexivity.
Qed.

(*Alternate phrasing of the lemma using an inductive predicate for
  elaboration suceeding, instead of the "exists a, elaborate ... = Some a"
  I think it should be equivalent, but for this one most steps go through easier.
*)
Lemma alt_well_scoped (cst : cst_term) (ctx : list string) 
(x : StrSet.Subset (cst_variables cst) (StrSProp.of_list ctx)) :
 elab_success cst ctx.
Proof.
  induction cst.
  all : simpl ; trivial.
  simpl in x.
  assert (StrSet.In s (StrSProp.of_list ctx)).
  apply x.
  apply (StrSet.singleton_spec s s).
  reflexivity.
  destruct ( (StrSProp.of_list_1 ctx s)).
  destruct (InA_alt eq s ctx).
  destruct (H2 (H0 H)).
  destruct H4.
  rewrite H4.
  exact H5.

  exact (IHcst x).
  simpl in x.

   (* I can't figure out how to get past this step 
     1: I'm not sure what I can do to make use of the induction hypothesis here
     Since we only know that the free variables minus s is a subset of the context,
     and not that the whole set of free variables is.
     2: If I can get the induction hypothesis to work, I need a lemma of the form
     (elab_success cst ctx) -> (elab_success cst (s::ctx)), which I haven't been able to prove either.
  *)
  

  
  2 : {
    split.
    simpl in x.

    assert (StrSet.Subset (cst_variables cst1) (cst_variables (cApp cst1 cst2))).
    simpl.
    apply StrSProp.union_subset_1.
    exact (IHcst1 (StrSProp.subset_trans H x)).

    assert (StrSet.Subset (cst_variables cst2) (cst_variables (cApp cst1 cst2))).
    simpl.
    apply StrSProp.union_subset_2.
    exact (IHcst2 (StrSProp.subset_trans H x)).
  }

  
  (* Partial work on proof by cases that could be useful later
     Still gets stuck on essentially the same step as without looking at the cases
  destruct cst.
  all : simpl ; trivial.
  destruct (String.string_dec s s0).
  left.
  exact e.
  right.
  
  simpl in x.
  unfold StrSet.Subset in x.
  assert (StrSet.In s0 (StrSProp.of_list ctx)).
  apply (x s0).
  rewrite (StrSet.remove_spec).
  split.
  apply StrSet.singleton_spec.
  auto.
  auto.
  
  destruct ( (StrSProp.of_list_1 ctx s0)).
  destruct (InA_alt eq s0 ctx).
  destruct (H2 (H0 H)).
  destruct H4.
  rewrite H4.
  exact H5.
  *)
  

 
  

  
  (*Admitted just so the lower proof attempt isn't blocked*)
Admitted.


(* If all free variables are in a context, then elaboration suceeds with that context*)
Lemma well_scoped (cst : cst_term) (ctx : list string) 
(x : StrSet.Subset (cst_variables cst) (StrSProp.of_list ctx)) :
exists a : ast_term, (elaborate cst ctx = Some a).
Proof.
  induction cst.

  exists (aType level).
  reflexivity.
 
  

  exists (aNat).
  reflexivity.

  
  assert (StrSet.In s (cst_variables (cVar s))). {
    simpl.
    apply (StrSet.singleton_spec).
    reflexivity. }
  assert (In s ctx). {
    assert (Q:=StrSProp.of_list_1 ctx s).
    assert (InA eq s ctx -> In s ctx).
    intro.
    rewrite (InA_alt eq s ctx) in H0.
    destruct H0.
    destruct H0.
    rewrite <- H0 in H1.
    exact H1.
    rewrite <- Q in H0.
    apply H0.
    auto. }


  destruct (lookup_known s ctx H0).
  exists (aVar x0).
  simpl.
  rewrite H1.
  reflexivity.
  
  exists aZero.
  reflexivity.

  destruct (IHcst x).
  exists (aSucc x0).
  simpl.
  rewrite H.
  reflexivity.

  simpl in x.
  (*This is basically the same stuck situation as before, where I don't 
    quite know how to apply the induction hypothesis, and I still need
    the fact that if the elaboration succeeds with ctx it also succeeds with s::ctx *)
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




