  

Require Import String.
Require Import List.

Module Cst.
Inductive obj :=
  | TType : nat -> obj
  | Nat : obj
  | Zero : obj
  | Succ : obj -> obj
  | App : obj -> obj -> obj
  | Fun : string -> obj -> obj -> obj
  | Pi : string -> obj -> obj -> obj
  | Var : string -> obj.
End Cst.



From Coq.Lists Require List.
From Coq.PArith Require Import BinPos.
From Coq.NArith Require Import BinNat.
From MenhirLib Require Main.
From MenhirLib Require Version.
Import List.ListNotations.

Definition version_check : unit := MenhirLib.Version.require_20220210.

Unset Elimination Schemes.

Inductive token : Type :=
| ZERO : unit%type -> token
| VAR :        (string)%type -> token
| TYPE : unit%type -> token
| SUCC : unit%type -> token
| RPAREN : unit%type -> token
| PI : unit%type -> token
| NAT : unit%type -> token
| LPAREN : unit%type -> token
| LAMBDA : unit%type -> token
| INT :        (nat)%type -> token
| EOF : unit%type -> token
| DOT : unit%type -> token
| COLON : unit%type -> token.

Module Import Gram <: MenhirLib.Grammar.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Inductive terminal' : Set :=
| COLON't
| DOT't
| EOF't
| INT't
| LAMBDA't
| LPAREN't
| NAT't
| PI't
| RPAREN't
| SUCC't
| TYPE't
| VAR't
| ZERO't.
Definition terminal := terminal'.

Global Program Instance terminalNum : MenhirLib.Alphabet.Numbered terminal :=
  { inj := fun x => match x return _ with
    | COLON't => 1%positive
    | DOT't => 2%positive
    | EOF't => 3%positive
    | INT't => 4%positive
    | LAMBDA't => 5%positive
    | LPAREN't => 6%positive
    | NAT't => 7%positive
    | PI't => 8%positive
    | RPAREN't => 9%positive
    | SUCC't => 10%positive
    | TYPE't => 11%positive
    | VAR't => 12%positive
    | ZERO't => 13%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => COLON't
    | 2%positive => DOT't
    | 3%positive => EOF't
    | 4%positive => INT't
    | 5%positive => LAMBDA't
    | 6%positive => LPAREN't
    | 7%positive => NAT't
    | 8%positive => PI't
    | 9%positive => RPAREN't
    | 10%positive => SUCC't
    | 11%positive => TYPE't
    | 12%positive => VAR't
    | 13%positive => ZERO't
    | _ => COLON't
    end)%Z;
    inj_bound := 13%positive }.
Global Instance TerminalAlph : MenhirLib.Alphabet.Alphabet terminal := _.

Inductive nonterminal' : Set :=
| app_obj'nt
| args_list'nt
| args_obj'nt
| obj'nt
| prog'nt
| rev_args_list'nt
| simpl_obj'nt.
Definition nonterminal := nonterminal'.

Global Program Instance nonterminalNum : MenhirLib.Alphabet.Numbered nonterminal :=
  { inj := fun x => match x return _ with
    | app_obj'nt => 1%positive
    | args_list'nt => 2%positive
    | args_obj'nt => 3%positive
    | obj'nt => 4%positive
    | prog'nt => 5%positive
    | rev_args_list'nt => 6%positive
    | simpl_obj'nt => 7%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => app_obj'nt
    | 2%positive => args_list'nt
    | 3%positive => args_obj'nt
    | 4%positive => obj'nt
    | 5%positive => prog'nt
    | 6%positive => rev_args_list'nt
    | 7%positive => simpl_obj'nt
    | _ => app_obj'nt
    end)%Z;
    inj_bound := 7%positive }.
Global Instance NonTerminalAlph : MenhirLib.Alphabet.Alphabet nonterminal := _.

Include MenhirLib.Grammar.Symbol.

Definition terminal_semantic_type (t:terminal) : Type:=
  match t with
  | ZERO't => unit%type
  | VAR't =>        (string)%type
  | TYPE't => unit%type
  | SUCC't => unit%type
  | RPAREN't => unit%type
  | PI't => unit%type
  | NAT't => unit%type
  | LPAREN't => unit%type
  | LAMBDA't => unit%type
  | INT't =>        (nat)%type
  | EOF't => unit%type
  | DOT't => unit%type
  | COLON't => unit%type
  end.

Definition nonterminal_semantic_type (nt:nonterminal) : Type:=
  match nt with
  | simpl_obj'nt =>       (Cst.obj)%type
  | rev_args_list'nt =>       (list (string * Cst.obj))%type
  | prog'nt =>        (Cst.obj)%type
  | obj'nt =>       (Cst.obj)%type
  | args_obj'nt =>       (string * Cst.obj)%type
  | args_list'nt =>       (list (string * Cst.obj))%type
  | app_obj'nt =>       (Cst.obj)%type
  end.

Definition symbol_semantic_type (s:symbol) : Type:=
  match s with
  | T t => terminal_semantic_type t
  | NT nt => nonterminal_semantic_type nt
  end.

Definition token := token.

Definition token_term (tok : token) : terminal :=
  match tok with
  | ZERO _ => ZERO't
  | VAR _ => VAR't
  | TYPE _ => TYPE't
  | SUCC _ => SUCC't
  | RPAREN _ => RPAREN't
  | PI _ => PI't
  | NAT _ => NAT't
  | LPAREN _ => LPAREN't
  | LAMBDA _ => LAMBDA't
  | INT _ => INT't
  | EOF _ => EOF't
  | DOT _ => DOT't
  | COLON _ => COLON't
  end.

Definition token_sem (tok : token) : symbol_semantic_type (T (token_term tok)) :=
  match tok with
  | ZERO x => x
  | VAR x => x
  | TYPE x => x
  | SUCC x => x
  | RPAREN x => x
  | PI x => x
  | NAT x => x
  | LPAREN x => x
  | LAMBDA x => x
  | INT x => x
  | EOF x => x
  | DOT x => x
  | COLON x => x
  end.

Inductive production' : Set :=
| Prod'simpl_obj'5
| Prod'simpl_obj'4
| Prod'simpl_obj'3
| Prod'simpl_obj'2
| Prod'simpl_obj'1
| Prod'simpl_obj'0
| Prod'rev_args_list'1
| Prod'rev_args_list'0
| Prod'prog'0
| Prod'obj'2
| Prod'obj'1
| Prod'obj'0
| Prod'args_obj'0
| Prod'args_list'0
| Prod'app_obj'1
| Prod'app_obj'0.
Definition production := production'.

Global Program Instance productionNum : MenhirLib.Alphabet.Numbered production :=
  { inj := fun x => match x return _ with
    | Prod'simpl_obj'5 => 1%positive
    | Prod'simpl_obj'4 => 2%positive
    | Prod'simpl_obj'3 => 3%positive
    | Prod'simpl_obj'2 => 4%positive
    | Prod'simpl_obj'1 => 5%positive
    | Prod'simpl_obj'0 => 6%positive
    | Prod'rev_args_list'1 => 7%positive
    | Prod'rev_args_list'0 => 8%positive
    | Prod'prog'0 => 9%positive
    | Prod'obj'2 => 10%positive
    | Prod'obj'1 => 11%positive
    | Prod'obj'0 => 12%positive
    | Prod'args_obj'0 => 13%positive
    | Prod'args_list'0 => 14%positive
    | Prod'app_obj'1 => 15%positive
    | Prod'app_obj'0 => 16%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Prod'simpl_obj'5
    | 2%positive => Prod'simpl_obj'4
    | 3%positive => Prod'simpl_obj'3
    | 4%positive => Prod'simpl_obj'2
    | 5%positive => Prod'simpl_obj'1
    | 6%positive => Prod'simpl_obj'0
    | 7%positive => Prod'rev_args_list'1
    | 8%positive => Prod'rev_args_list'0
    | 9%positive => Prod'prog'0
    | 10%positive => Prod'obj'2
    | 11%positive => Prod'obj'1
    | 12%positive => Prod'obj'0
    | 13%positive => Prod'args_obj'0
    | 14%positive => Prod'args_list'0
    | 15%positive => Prod'app_obj'1
    | 16%positive => Prod'app_obj'0
    | _ => Prod'simpl_obj'5
    end)%Z;
    inj_bound := 16%positive }.
Global Instance ProductionAlph : MenhirLib.Alphabet.Alphabet production := _.

Definition prod_contents (p:production) :
  { p:nonterminal * list symbol &
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) }
 :=
  let box := existT (fun p =>
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) )
  in
  match p with
  | Prod'app_obj'0 => box
    (app_obj'nt, [NT simpl_obj'nt; NT app_obj'nt]%list)
    (fun _2 _1 =>
                      ( Cst.App _1 _2 )
)
  | Prod'app_obj'1 => box
    (app_obj'nt, [NT simpl_obj'nt]%list)
    (fun _1 =>
              ( _1 )
)
  | Prod'args_list'0 => box
    (args_list'nt, [NT rev_args_list'nt]%list)
    (fun _1 =>
                  ( List.rev _1 )
)
  | Prod'args_obj'0 => box
    (args_obj'nt, [T RPAREN't; NT obj'nt; T COLON't; T VAR't; T LPAREN't]%list)
    (fun _5 _4 _3 _2 _1 =>
                                ( (_2, _4) )
)
  | Prod'obj'0 => box
    (obj'nt, [NT obj'nt; T DOT't; NT args_list'nt; T LAMBDA't]%list)
    (fun _4 _3 _2 _1 =>
                             (
      List.fold_left (fun acc arg => Cst.Fun (fst arg) (snd arg) acc) _2 _4 
  )
)
  | Prod'obj'1 => box
    (obj'nt, [NT obj'nt; T DOT't; NT args_list'nt; T PI't]%list)
    (fun _4 _3 _2 _1 =>
                         (
      List.fold_left (fun acc arg => Cst.Pi (fst arg) (snd arg) acc) _2 _4
  )
)
  | Prod'obj'2 => box
    (obj'nt, [NT app_obj'nt]%list)
    (fun _1 =>
            ( _1 )
)
  | Prod'prog'0 => box
    (prog'nt, [T EOF't; NT obj'nt]%list)
    (fun _2 _1 =>
            ( _1 )
)
  | Prod'rev_args_list'0 => box
    (rev_args_list'nt, [NT args_obj'nt; NT rev_args_list'nt]%list)
    (fun _2 _1 =>
                           ( _2 :: _1 )
)
  | Prod'rev_args_list'1 => box
    (rev_args_list'nt, [NT args_obj'nt]%list)
    (fun _1 =>
             ( [_1] )
)
  | Prod'simpl_obj'0 => box
    (simpl_obj'nt, [T VAR't]%list)
    (fun _1 =>
        ( Cst.Var _1 )
)
  | Prod'simpl_obj'1 => box
    (simpl_obj'nt, [T NAT't]%list)
    (fun _1 =>
        ( Cst.Nat )
)
  | Prod'simpl_obj'2 => box
    (simpl_obj'nt, [T ZERO't]%list)
    (fun _1 =>
         ( Cst.Zero )
)
  | Prod'simpl_obj'3 => box
    (simpl_obj'nt, [T INT't; T TYPE't]%list)
    (fun _2 _1 =>
             ( Cst.TType _2 )
)
  | Prod'simpl_obj'4 => box
    (simpl_obj'nt, [NT simpl_obj'nt; T SUCC't]%list)
    (fun _2 _1 =>
                   ( Cst.Succ _2 )
)
  | Prod'simpl_obj'5 => box
    (simpl_obj'nt, [T RPAREN't; NT obj'nt; T LPAREN't]%list)
    (fun _3 _2 _1 =>
                      ( _2 )
)
  end.

Definition prod_lhs (p:production) :=
  fst (projT1 (prod_contents p)).
Definition prod_rhs_rev (p:production) :=
  snd (projT1 (prod_contents p)).
Definition prod_action (p:production) :=
  projT2 (prod_contents p).

Include MenhirLib.Grammar.Defs.

End Gram.

Module Aut <: MenhirLib.Automaton.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Module Gram := Gram.
Module GramDefs := Gram.

Definition nullable_nterm (nt:nonterminal) : bool :=
  match nt with
  | simpl_obj'nt => false
  | rev_args_list'nt => false
  | prog'nt => false
  | obj'nt => false
  | args_obj'nt => false
  | args_list'nt => false
  | app_obj'nt => false
  end.

Definition first_nterm (nt:nonterminal) : list terminal :=
  match nt with
  | simpl_obj'nt => [ZERO't; VAR't; TYPE't; SUCC't; NAT't; LPAREN't]%list
  | rev_args_list'nt => [LPAREN't]%list
  | prog'nt => [ZERO't; VAR't; TYPE't; SUCC't; PI't; NAT't; LPAREN't; LAMBDA't]%list
  | obj'nt => [ZERO't; VAR't; TYPE't; SUCC't; PI't; NAT't; LPAREN't; LAMBDA't]%list
  | args_obj'nt => [LPAREN't]%list
  | args_list'nt => [LPAREN't]%list
  | app_obj'nt => [ZERO't; VAR't; TYPE't; SUCC't; NAT't; LPAREN't]%list
  end.

Inductive noninitstate' : Set :=
| Nis'32
| Nis'31
| Nis'29
| Nis'28
| Nis'27
| Nis'26
| Nis'25
| Nis'24
| Nis'23
| Nis'22
| Nis'21
| Nis'20
| Nis'19
| Nis'18
| Nis'17
| Nis'16
| Nis'15
| Nis'14
| Nis'13
| Nis'12
| Nis'11
| Nis'10
| Nis'9
| Nis'8
| Nis'7
| Nis'6
| Nis'5
| Nis'4
| Nis'3
| Nis'2
| Nis'1.
Definition noninitstate := noninitstate'.

Global Program Instance noninitstateNum : MenhirLib.Alphabet.Numbered noninitstate :=
  { inj := fun x => match x return _ with
    | Nis'32 => 1%positive
    | Nis'31 => 2%positive
    | Nis'29 => 3%positive
    | Nis'28 => 4%positive
    | Nis'27 => 5%positive
    | Nis'26 => 6%positive
    | Nis'25 => 7%positive
    | Nis'24 => 8%positive
    | Nis'23 => 9%positive
    | Nis'22 => 10%positive
    | Nis'21 => 11%positive
    | Nis'20 => 12%positive
    | Nis'19 => 13%positive
    | Nis'18 => 14%positive
    | Nis'17 => 15%positive
    | Nis'16 => 16%positive
    | Nis'15 => 17%positive
    | Nis'14 => 18%positive
    | Nis'13 => 19%positive
    | Nis'12 => 20%positive
    | Nis'11 => 21%positive
    | Nis'10 => 22%positive
    | Nis'9 => 23%positive
    | Nis'8 => 24%positive
    | Nis'7 => 25%positive
    | Nis'6 => 26%positive
    | Nis'5 => 27%positive
    | Nis'4 => 28%positive
    | Nis'3 => 29%positive
    | Nis'2 => 30%positive
    | Nis'1 => 31%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Nis'32
    | 2%positive => Nis'31
    | 3%positive => Nis'29
    | 4%positive => Nis'28
    | 5%positive => Nis'27
    | 6%positive => Nis'26
    | 7%positive => Nis'25
    | 8%positive => Nis'24
    | 9%positive => Nis'23
    | 10%positive => Nis'22
    | 11%positive => Nis'21
    | 12%positive => Nis'20
    | 13%positive => Nis'19
    | 14%positive => Nis'18
    | 15%positive => Nis'17
    | 16%positive => Nis'16
    | 17%positive => Nis'15
    | 18%positive => Nis'14
    | 19%positive => Nis'13
    | 20%positive => Nis'12
    | 21%positive => Nis'11
    | 22%positive => Nis'10
    | 23%positive => Nis'9
    | 24%positive => Nis'8
    | 25%positive => Nis'7
    | 26%positive => Nis'6
    | 27%positive => Nis'5
    | 28%positive => Nis'4
    | 29%positive => Nis'3
    | 30%positive => Nis'2
    | 31%positive => Nis'1
    | _ => Nis'32
    end)%Z;
    inj_bound := 31%positive }.
Global Instance NonInitStateAlph : MenhirLib.Alphabet.Alphabet noninitstate := _.

Definition last_symb_of_non_init_state (noninitstate:noninitstate) : symbol :=
  match noninitstate with
  | Nis'1 => T ZERO't
  | Nis'2 => T VAR't
  | Nis'3 => T TYPE't
  | Nis'4 => T INT't
  | Nis'5 => T SUCC't
  | Nis'6 => T NAT't
  | Nis'7 => T LPAREN't
  | Nis'8 => T PI't
  | Nis'9 => T LPAREN't
  | Nis'10 => T VAR't
  | Nis'11 => T COLON't
  | Nis'12 => T LAMBDA't
  | Nis'13 => NT rev_args_list'nt
  | Nis'14 => NT args_obj'nt
  | Nis'15 => NT args_obj'nt
  | Nis'16 => NT args_list'nt
  | Nis'17 => T DOT't
  | Nis'18 => NT simpl_obj'nt
  | Nis'19 => NT obj'nt
  | Nis'20 => NT app_obj'nt
  | Nis'21 => NT simpl_obj'nt
  | Nis'22 => NT obj'nt
  | Nis'23 => T RPAREN't
  | Nis'24 => NT args_list'nt
  | Nis'25 => T DOT't
  | Nis'26 => NT obj'nt
  | Nis'27 => NT obj'nt
  | Nis'28 => T RPAREN't
  | Nis'29 => NT simpl_obj'nt
  | Nis'31 => NT obj'nt
  | Nis'32 => T EOF't
  end.

Inductive initstate' : Set :=
| Init'0.
Definition initstate := initstate'.

Global Program Instance initstateNum : MenhirLib.Alphabet.Numbered initstate :=
  { inj := fun x => match x return _ with
    | Init'0 => 1%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Init'0
    | _ => Init'0
    end)%Z;
    inj_bound := 1%positive }.
Global Instance InitStateAlph : MenhirLib.Alphabet.Alphabet initstate := _.

Include MenhirLib.Automaton.Types.

Definition start_nt (init:initstate) : nonterminal :=
  match init with
  | Init'0 => prog'nt
  end.

Definition action_table (state:state) : action :=
  match state with
  | Init Init'0 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'5 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'6 (eq_refl _)
    | LPAREN't => Shift_act Nis'7 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'1 => Default_reduce_act Prod'simpl_obj'2
  | Ninit Nis'2 => Default_reduce_act Prod'simpl_obj'0
  | Ninit Nis'3 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | INT't => Shift_act Nis'4 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'4 => Default_reduce_act Prod'simpl_obj'3
  | Ninit Nis'5 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'5 (eq_refl _)
    | NAT't => Shift_act Nis'6 (eq_refl _)
    | LPAREN't => Shift_act Nis'7 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'6 => Default_reduce_act Prod'simpl_obj'1
  | Ninit Nis'7 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'5 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'6 (eq_refl _)
    | LPAREN't => Shift_act Nis'7 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'8 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'9 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | VAR't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'10 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'11 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'11 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'5 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'6 (eq_refl _)
    | LPAREN't => Shift_act Nis'7 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'12 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'13 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'9 (eq_refl _)
    | DOT't => Reduce_act Prod'args_list'0
    | _ => Fail_act
    end)
  | Ninit Nis'14 => Default_reduce_act Prod'rev_args_list'0
  | Ninit Nis'15 => Default_reduce_act Prod'rev_args_list'1
  | Ninit Nis'16 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'17 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'17 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'5 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'6 (eq_refl _)
    | LPAREN't => Shift_act Nis'7 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'18 => Default_reduce_act Prod'app_obj'1
  | Ninit Nis'19 => Default_reduce_act Prod'obj'0
  | Ninit Nis'20 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'5 (eq_refl _)
    | RPAREN't => Reduce_act Prod'obj'2
    | NAT't => Shift_act Nis'6 (eq_refl _)
    | LPAREN't => Shift_act Nis'7 (eq_refl _)
    | EOF't => Reduce_act Prod'obj'2
    | _ => Fail_act
    end)
  | Ninit Nis'21 => Default_reduce_act Prod'app_obj'0
  | Ninit Nis'22 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'23 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'23 => Default_reduce_act Prod'args_obj'0
  | Ninit Nis'24 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'25 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'25 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | VAR't => Shift_act Nis'2 (eq_refl _)
    | TYPE't => Shift_act Nis'3 (eq_refl _)
    | SUCC't => Shift_act Nis'5 (eq_refl _)
    | PI't => Shift_act Nis'8 (eq_refl _)
    | NAT't => Shift_act Nis'6 (eq_refl _)
    | LPAREN't => Shift_act Nis'7 (eq_refl _)
    | LAMBDA't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'26 => Default_reduce_act Prod'obj'1
  | Ninit Nis'27 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'28 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'28 => Default_reduce_act Prod'simpl_obj'5
  | Ninit Nis'29 => Default_reduce_act Prod'simpl_obj'4
  | Ninit Nis'31 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | EOF't => Shift_act Nis'32 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'32 => Default_reduce_act Prod'prog'0
  end.

Definition goto_table (state:state) (nt:nonterminal) :=
  match state, nt return option { s:noninitstate | NT nt = last_symb_of_non_init_state s } with
  | Init Init'0, simpl_obj'nt => Some (exist _ Nis'18 (eq_refl _))
  | Init Init'0, prog'nt => None  | Init Init'0, obj'nt => Some (exist _ Nis'31 (eq_refl _))
  | Init Init'0, app_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'5, simpl_obj'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'7, simpl_obj'nt => Some (exist _ Nis'18 (eq_refl _))
  | Ninit Nis'7, obj'nt => Some (exist _ Nis'27 (eq_refl _))
  | Ninit Nis'7, app_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'8, rev_args_list'nt => Some (exist _ Nis'13 (eq_refl _))
  | Ninit Nis'8, args_obj'nt => Some (exist _ Nis'15 (eq_refl _))
  | Ninit Nis'8, args_list'nt => Some (exist _ Nis'24 (eq_refl _))
  | Ninit Nis'11, simpl_obj'nt => Some (exist _ Nis'18 (eq_refl _))
  | Ninit Nis'11, obj'nt => Some (exist _ Nis'22 (eq_refl _))
  | Ninit Nis'11, app_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'12, rev_args_list'nt => Some (exist _ Nis'13 (eq_refl _))
  | Ninit Nis'12, args_obj'nt => Some (exist _ Nis'15 (eq_refl _))
  | Ninit Nis'12, args_list'nt => Some (exist _ Nis'16 (eq_refl _))
  | Ninit Nis'13, args_obj'nt => Some (exist _ Nis'14 (eq_refl _))
  | Ninit Nis'17, simpl_obj'nt => Some (exist _ Nis'18 (eq_refl _))
  | Ninit Nis'17, obj'nt => Some (exist _ Nis'19 (eq_refl _))
  | Ninit Nis'17, app_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | Ninit Nis'20, simpl_obj'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'25, simpl_obj'nt => Some (exist _ Nis'18 (eq_refl _))
  | Ninit Nis'25, obj'nt => Some (exist _ Nis'26 (eq_refl _))
  | Ninit Nis'25, app_obj'nt => Some (exist _ Nis'20 (eq_refl _))
  | _, _ => None
  end.

Definition past_symb_of_non_init_state (noninitstate:noninitstate) : list symbol :=
  match noninitstate with
  | Nis'1 => []%list
  | Nis'2 => []%list
  | Nis'3 => []%list
  | Nis'4 => [T TYPE't]%list
  | Nis'5 => []%list
  | Nis'6 => []%list
  | Nis'7 => []%list
  | Nis'8 => []%list
  | Nis'9 => []%list
  | Nis'10 => [T LPAREN't]%list
  | Nis'11 => [T VAR't; T LPAREN't]%list
  | Nis'12 => []%list
  | Nis'13 => []%list
  | Nis'14 => [NT rev_args_list'nt]%list
  | Nis'15 => []%list
  | Nis'16 => [T LAMBDA't]%list
  | Nis'17 => [NT args_list'nt; T LAMBDA't]%list
  | Nis'18 => []%list
  | Nis'19 => [T DOT't; NT args_list'nt; T LAMBDA't]%list
  | Nis'20 => []%list
  | Nis'21 => [NT app_obj'nt]%list
  | Nis'22 => [T COLON't; T VAR't; T LPAREN't]%list
  | Nis'23 => [NT obj'nt; T COLON't; T VAR't; T LPAREN't]%list
  | Nis'24 => [T PI't]%list
  | Nis'25 => [NT args_list'nt; T PI't]%list
  | Nis'26 => [T DOT't; NT args_list'nt; T PI't]%list
  | Nis'27 => [T LPAREN't]%list
  | Nis'28 => [NT obj'nt; T LPAREN't]%list
  | Nis'29 => [T SUCC't]%list
  | Nis'31 => []%list
  | Nis'32 => [NT obj'nt]%list
  end.
Extract Constant past_symb_of_non_init_state => "fun _ -> assert false".

Definition state_set_1 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'5 | Ninit Nis'7 | Ninit Nis'11 | Ninit Nis'17 | Ninit Nis'20 | Ninit Nis'25 => true
  | _ => false
  end.
Extract Inlined Constant state_set_1 => "assert false".

Definition state_set_2 (s:state) : bool :=
  match s with
  | Ninit Nis'3 => true
  | _ => false
  end.
Extract Inlined Constant state_set_2 => "assert false".

Definition state_set_3 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'7 | Ninit Nis'11 | Ninit Nis'17 | Ninit Nis'25 => true
  | _ => false
  end.
Extract Inlined Constant state_set_3 => "assert false".

Definition state_set_4 (s:state) : bool :=
  match s with
  | Ninit Nis'8 | Ninit Nis'12 | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_4 => "assert false".

Definition state_set_5 (s:state) : bool :=
  match s with
  | Ninit Nis'9 => true
  | _ => false
  end.
Extract Inlined Constant state_set_5 => "assert false".

Definition state_set_6 (s:state) : bool :=
  match s with
  | Ninit Nis'10 => true
  | _ => false
  end.
Extract Inlined Constant state_set_6 => "assert false".

Definition state_set_7 (s:state) : bool :=
  match s with
  | Ninit Nis'8 | Ninit Nis'12 => true
  | _ => false
  end.
Extract Inlined Constant state_set_7 => "assert false".

Definition state_set_8 (s:state) : bool :=
  match s with
  | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_8 => "assert false".

Definition state_set_9 (s:state) : bool :=
  match s with
  | Ninit Nis'12 => true
  | _ => false
  end.
Extract Inlined Constant state_set_9 => "assert false".

Definition state_set_10 (s:state) : bool :=
  match s with
  | Ninit Nis'16 => true
  | _ => false
  end.
Extract Inlined Constant state_set_10 => "assert false".

Definition state_set_11 (s:state) : bool :=
  match s with
  | Ninit Nis'17 => true
  | _ => false
  end.
Extract Inlined Constant state_set_11 => "assert false".

Definition state_set_12 (s:state) : bool :=
  match s with
  | Ninit Nis'20 => true
  | _ => false
  end.
Extract Inlined Constant state_set_12 => "assert false".

Definition state_set_13 (s:state) : bool :=
  match s with
  | Ninit Nis'11 => true
  | _ => false
  end.
Extract Inlined Constant state_set_13 => "assert false".

Definition state_set_14 (s:state) : bool :=
  match s with
  | Ninit Nis'22 => true
  | _ => false
  end.
Extract Inlined Constant state_set_14 => "assert false".

Definition state_set_15 (s:state) : bool :=
  match s with
  | Ninit Nis'8 => true
  | _ => false
  end.
Extract Inlined Constant state_set_15 => "assert false".

Definition state_set_16 (s:state) : bool :=
  match s with
  | Ninit Nis'24 => true
  | _ => false
  end.
Extract Inlined Constant state_set_16 => "assert false".

Definition state_set_17 (s:state) : bool :=
  match s with
  | Ninit Nis'25 => true
  | _ => false
  end.
Extract Inlined Constant state_set_17 => "assert false".

Definition state_set_18 (s:state) : bool :=
  match s with
  | Ninit Nis'7 => true
  | _ => false
  end.
Extract Inlined Constant state_set_18 => "assert false".

Definition state_set_19 (s:state) : bool :=
  match s with
  | Ninit Nis'27 => true
  | _ => false
  end.
Extract Inlined Constant state_set_19 => "assert false".

Definition state_set_20 (s:state) : bool :=
  match s with
  | Ninit Nis'5 => true
  | _ => false
  end.
Extract Inlined Constant state_set_20 => "assert false".

Definition state_set_21 (s:state) : bool :=
  match s with
  | Init Init'0 => true
  | _ => false
  end.
Extract Inlined Constant state_set_21 => "assert false".

Definition state_set_22 (s:state) : bool :=
  match s with
  | Ninit Nis'31 => true
  | _ => false
  end.
Extract Inlined Constant state_set_22 => "assert false".

Definition past_state_of_non_init_state (s:noninitstate) : list (state -> bool) :=
  match s with
  | Nis'1 => [state_set_1]%list
  | Nis'2 => [state_set_1]%list
  | Nis'3 => [state_set_1]%list
  | Nis'4 => [state_set_2; state_set_1]%list
  | Nis'5 => [state_set_1]%list
  | Nis'6 => [state_set_1]%list
  | Nis'7 => [state_set_1]%list
  | Nis'8 => [state_set_3]%list
  | Nis'9 => [state_set_4]%list
  | Nis'10 => [state_set_5; state_set_4]%list
  | Nis'11 => [state_set_6; state_set_5; state_set_4]%list
  | Nis'12 => [state_set_3]%list
  | Nis'13 => [state_set_7]%list
  | Nis'14 => [state_set_8; state_set_7]%list
  | Nis'15 => [state_set_7]%list
  | Nis'16 => [state_set_9; state_set_3]%list
  | Nis'17 => [state_set_10; state_set_9; state_set_3]%list
  | Nis'18 => [state_set_3]%list
  | Nis'19 => [state_set_11; state_set_10; state_set_9; state_set_3]%list
  | Nis'20 => [state_set_3]%list
  | Nis'21 => [state_set_12; state_set_3]%list
  | Nis'22 => [state_set_13; state_set_6; state_set_5; state_set_4]%list
  | Nis'23 => [state_set_14; state_set_13; state_set_6; state_set_5; state_set_4]%list
  | Nis'24 => [state_set_15; state_set_3]%list
  | Nis'25 => [state_set_16; state_set_15; state_set_3]%list
  | Nis'26 => [state_set_17; state_set_16; state_set_15; state_set_3]%list
  | Nis'27 => [state_set_18; state_set_1]%list
  | Nis'28 => [state_set_19; state_set_18; state_set_1]%list
  | Nis'29 => [state_set_20; state_set_1]%list
  | Nis'31 => [state_set_21]%list
  | Nis'32 => [state_set_22; state_set_21]%list
  end.
Extract Constant past_state_of_non_init_state => "fun _ -> assert false".

Definition lookahead_set_1 : list terminal :=
  [ZERO't; VAR't; TYPE't; SUCC't; NAT't; LPAREN't; EOF't]%list.
Extract Inlined Constant lookahead_set_1 => "assert false".

Definition lookahead_set_2 : list terminal :=
  [EOF't]%list.
Extract Inlined Constant lookahead_set_2 => "assert false".

Definition lookahead_set_3 : list terminal :=
  [ZERO't; VAR't; TYPE't; SUCC't; RPAREN't; PI't; NAT't; LPAREN't; LAMBDA't; INT't; EOF't; DOT't; COLON't]%list.
Extract Inlined Constant lookahead_set_3 => "assert false".

Definition lookahead_set_4 : list terminal :=
  [ZERO't; VAR't; TYPE't; SUCC't; RPAREN't; NAT't; LPAREN't; EOF't]%list.
Extract Inlined Constant lookahead_set_4 => "assert false".

Definition lookahead_set_5 : list terminal :=
  [ZERO't; VAR't; TYPE't; SUCC't; RPAREN't; NAT't; LPAREN't]%list.
Extract Inlined Constant lookahead_set_5 => "assert false".

Definition lookahead_set_6 : list terminal :=
  [RPAREN't]%list.
Extract Inlined Constant lookahead_set_6 => "assert false".

Definition lookahead_set_7 : list terminal :=
  [DOT't]%list.
Extract Inlined Constant lookahead_set_7 => "assert false".

Definition lookahead_set_8 : list terminal :=
  [LPAREN't; DOT't]%list.
Extract Inlined Constant lookahead_set_8 => "assert false".

Definition lookahead_set_9 : list terminal :=
  [RPAREN't; EOF't]%list.
Extract Inlined Constant lookahead_set_9 => "assert false".

Definition items_of_state_0 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'prog'0; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |};
    {| prod_item := Prod'simpl_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'simpl_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'simpl_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'simpl_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'simpl_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'simpl_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_0 => "assert false".

Definition items_of_state_1 : list item :=
  [ {| prod_item := Prod'simpl_obj'2; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_1 => "assert false".

Definition items_of_state_2 : list item :=
  [ {| prod_item := Prod'simpl_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_2 => "assert false".

Definition items_of_state_3 : list item :=
  [ {| prod_item := Prod'simpl_obj'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_3 => "assert false".

Definition items_of_state_4 : list item :=
  [ {| prod_item := Prod'simpl_obj'3; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_4 => "assert false".

Definition items_of_state_5 : list item :=
  [ {| prod_item := Prod'simpl_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_5 => "assert false".

Definition items_of_state_6 : list item :=
  [ {| prod_item := Prod'simpl_obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_6 => "assert false".

Definition items_of_state_7 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'simpl_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_7 => "assert false".

Definition items_of_state_8 : list item :=
  [ {| prod_item := Prod'args_list'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'args_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'rev_args_list'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'rev_args_list'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_8 => "assert false".

Definition items_of_state_9 : list item :=
  [ {| prod_item := Prod'args_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_9 => "assert false".

Definition items_of_state_10 : list item :=
  [ {| prod_item := Prod'args_obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_10 => "assert false".

Definition items_of_state_11 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'args_obj'0; dot_pos_item := 3; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'simpl_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'simpl_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_11 => "assert false".

Definition items_of_state_12 : list item :=
  [ {| prod_item := Prod'args_list'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'args_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'rev_args_list'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'rev_args_list'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_12 => "assert false".

Definition items_of_state_13 : list item :=
  [ {| prod_item := Prod'args_list'0; dot_pos_item := 1; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'args_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'rev_args_list'0; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_13 => "assert false".

Definition items_of_state_14 : list item :=
  [ {| prod_item := Prod'rev_args_list'0; dot_pos_item := 2; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_14 => "assert false".

Definition items_of_state_15 : list item :=
  [ {| prod_item := Prod'rev_args_list'1; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_15 => "assert false".

Definition items_of_state_16 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_16 => "assert false".

Definition items_of_state_17 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 3; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'simpl_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_17 => "assert false".

Definition items_of_state_18 : list item :=
  [ {| prod_item := Prod'app_obj'1; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_18 => "assert false".

Definition items_of_state_19 : list item :=
  [ {| prod_item := Prod'obj'0; dot_pos_item := 4; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_19 => "assert false".

Definition items_of_state_20 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 1; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'simpl_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_20 => "assert false".

Definition items_of_state_21 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_21 => "assert false".

Definition items_of_state_22 : list item :=
  [ {| prod_item := Prod'args_obj'0; dot_pos_item := 4; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_22 => "assert false".

Definition items_of_state_23 : list item :=
  [ {| prod_item := Prod'args_obj'0; dot_pos_item := 5; lookaheads_item := lookahead_set_8 |} ]%list.
Extract Inlined Constant items_of_state_23 => "assert false".

Definition items_of_state_24 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 2; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_24 => "assert false".

Definition items_of_state_25 : list item :=
  [ {| prod_item := Prod'app_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'app_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'1; dot_pos_item := 3; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'simpl_obj'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'simpl_obj'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_25 => "assert false".

Definition items_of_state_26 : list item :=
  [ {| prod_item := Prod'obj'1; dot_pos_item := 4; lookaheads_item := lookahead_set_9 |} ]%list.
Extract Inlined Constant items_of_state_26 => "assert false".

Definition items_of_state_27 : list item :=
  [ {| prod_item := Prod'simpl_obj'5; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_27 => "assert false".

Definition items_of_state_28 : list item :=
  [ {| prod_item := Prod'simpl_obj'5; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_28 => "assert false".

Definition items_of_state_29 : list item :=
  [ {| prod_item := Prod'simpl_obj'4; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_29 => "assert false".

Definition items_of_state_31 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 1; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_31 => "assert false".

Definition items_of_state_32 : list item :=
  [ {| prod_item := Prod'prog'0; dot_pos_item := 2; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_32 => "assert false".

Definition items_of_state (s:state) : list item :=
  match s with
  | Init Init'0 => items_of_state_0
  | Ninit Nis'1 => items_of_state_1
  | Ninit Nis'2 => items_of_state_2
  | Ninit Nis'3 => items_of_state_3
  | Ninit Nis'4 => items_of_state_4
  | Ninit Nis'5 => items_of_state_5
  | Ninit Nis'6 => items_of_state_6
  | Ninit Nis'7 => items_of_state_7
  | Ninit Nis'8 => items_of_state_8
  | Ninit Nis'9 => items_of_state_9
  | Ninit Nis'10 => items_of_state_10
  | Ninit Nis'11 => items_of_state_11
  | Ninit Nis'12 => items_of_state_12
  | Ninit Nis'13 => items_of_state_13
  | Ninit Nis'14 => items_of_state_14
  | Ninit Nis'15 => items_of_state_15
  | Ninit Nis'16 => items_of_state_16
  | Ninit Nis'17 => items_of_state_17
  | Ninit Nis'18 => items_of_state_18
  | Ninit Nis'19 => items_of_state_19
  | Ninit Nis'20 => items_of_state_20
  | Ninit Nis'21 => items_of_state_21
  | Ninit Nis'22 => items_of_state_22
  | Ninit Nis'23 => items_of_state_23
  | Ninit Nis'24 => items_of_state_24
  | Ninit Nis'25 => items_of_state_25
  | Ninit Nis'26 => items_of_state_26
  | Ninit Nis'27 => items_of_state_27
  | Ninit Nis'28 => items_of_state_28
  | Ninit Nis'29 => items_of_state_29
  | Ninit Nis'31 => items_of_state_31
  | Ninit Nis'32 => items_of_state_32
  end.
Extract Constant items_of_state => "fun _ -> assert false".

Definition N_of_state (s:state) : N :=
  match s with
  | Init Init'0 => 0%N
  | Ninit Nis'1 => 1%N
  | Ninit Nis'2 => 2%N
  | Ninit Nis'3 => 3%N
  | Ninit Nis'4 => 4%N
  | Ninit Nis'5 => 5%N
  | Ninit Nis'6 => 6%N
  | Ninit Nis'7 => 7%N
  | Ninit Nis'8 => 8%N
  | Ninit Nis'9 => 9%N
  | Ninit Nis'10 => 10%N
  | Ninit Nis'11 => 11%N
  | Ninit Nis'12 => 12%N
  | Ninit Nis'13 => 13%N
  | Ninit Nis'14 => 14%N
  | Ninit Nis'15 => 15%N
  | Ninit Nis'16 => 16%N
  | Ninit Nis'17 => 17%N
  | Ninit Nis'18 => 18%N
  | Ninit Nis'19 => 19%N
  | Ninit Nis'20 => 20%N
  | Ninit Nis'21 => 21%N
  | Ninit Nis'22 => 22%N
  | Ninit Nis'23 => 23%N
  | Ninit Nis'24 => 24%N
  | Ninit Nis'25 => 25%N
  | Ninit Nis'26 => 26%N
  | Ninit Nis'27 => 27%N
  | Ninit Nis'28 => 28%N
  | Ninit Nis'29 => 29%N
  | Ninit Nis'31 => 31%N
  | Ninit Nis'32 => 32%N
  end.
End Aut.

Module MenhirLibParser := MenhirLib.Main.Make Aut.
Theorem safe:
  MenhirLibParser.safe_validator tt = true.
Proof eq_refl true<:MenhirLibParser.safe_validator tt = true.

Theorem complete:
  MenhirLibParser.complete_validator tt = true.
Proof eq_refl true<:MenhirLibParser.complete_validator tt = true.

Definition prog : nat -> MenhirLibParser.Inter.buffer -> MenhirLibParser.Inter.parse_result        (Cst.obj) := MenhirLibParser.parse safe Aut.Init'0.

Theorem prog_correct (log_fuel : nat) (buffer : MenhirLibParser.Inter.buffer):
  match prog log_fuel buffer with
  | MenhirLibParser.Inter.Parsed_pr sem buffer_new =>
      exists word (tree : Gram.parse_tree (NT prog'nt) word),
        buffer = MenhirLibParser.Inter.app_buf word buffer_new /\
        Gram.pt_sem tree = sem
  | _ => True
  end.
Proof. apply MenhirLibParser.parse_correct with (init:=Aut.Init'0). Qed.

Theorem prog_complete (log_fuel : nat) (word : list token) (buffer_end : MenhirLibParser.Inter.buffer) :
  forall tree : Gram.parse_tree (NT prog'nt) word,
  match prog log_fuel (MenhirLibParser.Inter.app_buf word buffer_end) with
  | MenhirLibParser.Inter.Fail_pr => False
  | MenhirLibParser.Inter.Parsed_pr output_res buffer_end_res =>
      output_res = Gram.pt_sem tree /\
      buffer_end_res = buffer_end /\ (Gram.pt_size tree <= PeanoNat.Nat.pow 2 log_fuel)%nat
  | MenhirLibParser.Inter.Timeout_pr => (PeanoNat.Nat.pow 2 log_fuel < Gram.pt_size tree)%nat
  end.
Proof. apply MenhirLibParser.parse_complete with (init:=Aut.Init'0); exact complete. Qed.
