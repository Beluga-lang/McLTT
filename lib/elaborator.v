Require Export String.
Require Export List.
Require Export Coq.Structures.OrderedTypeEx.
Require Export MSets MSetInterface MSetFacts MSetProperties.
Require Export Arith.

Open Scope string_scope.


Module StrSet := Make String_as_OT.
Module StrSProp := MSetProperties.Properties StrSet.


Inductive cst_term : Type :=
 | cType (level : nat)
 | cNat
 | cVar (s : string)
 | cZero
 | cSucc (t : cst_term)
 | cFun (s : string) (t : cst_term)
 | cApp (t1 : cst_term) (t2 : cst_term).

Inductive ast_term : Type :=
 | aType (level : nat)
 | aNat
 | aVar (n : nat)
 | aZero
 | aSucc (t : ast_term)
 | aFun (t : ast_term)
 | aApp (t1 : ast_term) (t2 : ast_term).


(**De-monadify with pattern matching for now**)
Fixpoint lookup (s : string) (ctx : list string) (index : nat) : (option nat) :=
 match ctx with
  | nil => None
  | c::cs => if String.eqb c s then (Some index) else lookup s cs (index+1) 
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
 | cVar s =>  match lookup s ctx 0 with
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

Lemma lookup_immediate (s: string) (ctx: list string) (k : nat) : lookup s (s::ctx) k = Some k.
Proof.
  simpl.
  assert (se := String.eqb_eq s s).
  assert (b : s =? s = true).
  assert (ssym : s = s) by reflexivity.
  destruct se.
  exact (H0 ssym).
  rewrite b.
  reflexivity.
Qed.

Lemma lookup_next (s c: string) (ctx: list string) (neq : s <> c) (n: nat) : (lookup s ctx (n+1) = lookup s (c::ctx) (n)).
Proof.
  simpl.
  assert (c =? s = false).
  rewrite eqb_sym.
  apply String.eqb_neq.
  exact neq.
  rewrite H.
  reflexivity.
Qed.

Lemma additive_identity_unique (m n : nat) (e : m = m + n): (n = 0).
Proof.
  induction m.
  simpl in e.
  symmetry.
  exact e.
  inversion e.
  exact (IHm H0).
Qed.
Lemma lookup_lemma (s : string) (ctx: list string) (n m: nat) (p : lookup s ctx n = Some (n+m)) : lookup s ctx (n+1) = Some (n+m+1).
(*Proof.
  induction ctx as [| c ctx' IHctx].
  simpl.
  discriminate.

  assert (str_dec := String.string_dec s c).
  destruct str_dec.
  simpl.

  assert (eqcs : c =? s = true).
  apply (String.eqb_eq c s).
  symmetry.
  exact e.

  rewrite eqcs.
  
  
  assert (P := lookup_immediate c ctx').
  rewrite -> e in p.
  rewrite -> (P n) in p.
  assert(m=0). { inversion p. apply (additive_identity_unique n m H0). }
  rewrite H.
  auto.

  rewrite <- ((lookup_next s c ctx' n0 n)) in p.
  simpl.

  assert (c =? s = false).
    { rewrite eqb_sym. apply String.eqb_neq. exact n0. }

  rewrite H.

  assert (Q := lookup_next s c ctx' n0 n).
  *)
Admitted.

Lemma lookup_known (s : string) (ctx : list string) (p : List.In s ctx) : exists n : nat, (lookup s ctx 0 = Some n).
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
  
  assert (L:=(lookup_lemma s ctx' 0 x0) H3).
  simpl in L.
  exact L.
Qed.


(* If all free variables are in a context, then elaboration suceeds with that context*)
Lemma well_scoped (cst : cst_term) (ctx : list string) 
(x : StrSet.Subset (cst_variables cst) (StrSProp.of_list ctx)) :
exists a : ast_term, and (elaborate cst ctx = Some a) 
               (or ((max_index a) = None) (exists n : nat, and (max_index a = Some n) (n = StrSet.cardinal (cst_variables cst)))).
Proof.
  induction cst.

  exists (aType level).
  split.
  reflexivity.
  left.
  reflexivity.
  

  exists (aNat).
  split.
  reflexivity.
  left.
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
  split.
  reflexivity.
  right.
  exists 1.
  split.

  2: auto.

  
  
  
  (*exists aZero.
  auto.
  auto.
  assert (I := IHcst x).
  destruct I.
  exists (aSucc x0).
  simpl.
  rewrite H.
  reflexivity.

  assert(StrSet.Subset (cst_variables (cst)) (StrSProp.of_list ctx)) by admit.

  assert (I := IHcst H).
  destruct I.
  exists (aFun x0).
  simpl.
 
  
  assert (elaborate cst ctx = elaborate cst (s :: ctx)) by admit.
  
  rewrite <- H1.
  rewrite H0.
  reflexivity.
  
 
  assert (StrSet.Subset (cst_variables cst1) (cst_variables (cApp cst1 cst2))).
  simpl.
  apply StrSProp.union_subset_1.
  assert (S1 : StrSet.Subset (cst_variables cst1) (StrSProp.of_list ctx)).
  apply (StrSProp.subset_trans H x).
  destruct (IHcst1 S1).

  assert (StrSet.Subset (cst_variables cst2) (cst_variables (cApp cst1 cst2))).
  simpl.
  apply StrSProp.union_subset_2.
  assert (S2 : StrSet.Subset (cst_variables cst2) (StrSProp.of_list ctx)).
  apply (StrSProp.subset_trans H1 x).
  destruct (IHcst2 S2).
  
  exists(aApp x0 x1).
  simpl.
  rewrite H2.
  rewrite H0.
  reflexivity.*)
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




