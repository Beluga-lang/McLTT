(* Unit test cases for parsing *)

open Main
open McttExtracted.Entrypoint

(** Helper definitions *)

let main_of_example s = main_of_filename ("../examples/" ^ s)

(** Real tests *)
(* We never expect parser timeout. 2^500 fuel should be large enough! *)

let%expect_test "Type@0 is of Type@1" =
  let _ = main_of_program_string "Type@0 : Type@1" in
  [%expect
    {|
    Parsed:
      Type@0 : Type@1
    Elaborated:
      Type@0 : Type@1
    Normalized Result:
      Type@0 : Type@1
  |}]

let%expect_test "zero is of Nat" =
  let _ = main_of_program_string "zero : Nat" in
  [%expect
    {|
    Parsed:
      0 : Nat
    Elaborated:
      0 : Nat
    Normalized Result:
      0 : Nat
  |}]

let%expect_test "zero is not of Type@0" =
  let _ = main_of_program_string "zero : Type@0" in
  [%expect
    {|
    Type Checking Failure:
      0
    is not of
      Type@0
  |}]

let%expect_test "succ zero is of Nat" =
  let _ = main_of_program_string "succ zero : Nat" in
  [%expect
    {|
    Parsed:
      1 : Nat
    Elaborated:
      1 : Nat
    Normalized Result:
      1 : Nat
  |}]

let%expect_test "succ Type@0 is not of Nat (as it is ill-typed)" =
  let _ = main_of_program_string "succ Type@0 : Nat" in
  [%expect
    {|
    Type Checking Failure:
      succ Type@0
    is not of
      Nat
  |}]

let%expect_test "variable x is ill-scoped" =
  let _ = main_of_program_string "x : Type@0" in
  [%expect {|
    Elaboration Failure:
      x
    cannot be elaborated
  |}]

let%expect_test "identity function of Nat is of forall (x : Nat) -> Nat" =
  let _ = main_of_program_string "fun (y : Nat) -> y : forall (x : Nat) -> Nat" in
  [%expect
    {|
    Parsed:
      fun (y : Nat) -> y : forall (x : Nat) -> Nat
    Elaborated:
      fun (x1 : Nat) -> x1 : forall (x1 : Nat) -> Nat
    Normalized Result:
      fun (x1 : Nat) -> x1 : forall (x1 : Nat) -> Nat
  |}]

let%expect_test "recursion on a natural number that always returns zero is of \
                 Nat" =
  let _ = main_of_program_string
    "rec 3 return y . Nat | zero => 0 | succ n, r => 0 end : Nat" in
  [%expect
    {|
    Parsed:
      rec 3 return y . Nat | zero => 0 | succ n, r => 0 end : Nat
    Elaborated:
      rec 3 return x1 . Nat | zero => 0 | succ x2, x3 => 0 end : Nat
    Normalized Result:
      0 : Nat
  |}]

let%expect_test "simple_nat.mctt works" =
  let _ = main_of_example "simple_nat.mctt" in
  [%expect
    {|
    Parsed:
      4 : Nat
    Elaborated:
      4 : Nat
    Normalized Result:
      4 : Nat
  |}]

let%expect_test "simple_rec.mctt works" =
  let _ = main_of_example "simple_rec.mctt" in
  [%expect
    {|
    Parsed:
      fun (x : Nat) -> rec x return y . Nat | zero => 1 | succ n, r => succ r end
      : forall (x : Nat) -> Nat
    Elaborated:
      fun (x1 : Nat)
        -> rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end
      : forall (x1 : Nat) -> Nat
    Normalized Result:
      fun (x1 : Nat)
        -> rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end
      : forall (x1 : Nat) -> Nat
  |}]

let%expect_test "pair.mctt works" =
  let _ = main_of_example "pair.mctt" in
  [%expect
    {|
    Parsed:
      (fun (Pair : forall (A : Type@0)
                          (B : Type@0)
                     -> Type@1)
           (pair : forall (A : Type@0)
                          (B : Type@0)
                          (a : A)
                          (b : B)
                     -> Pair A B)
           (fst : forall (A : Type@0)
                         (B : Type@0)
                         (p : Pair A B)
                    -> A)
           (snd : forall (A : Type@0)
                         (B : Type@0)
                         (p : Pair A B)
                    -> B)
        -> (fun (p : Pair Nat (forall (x : Nat) -> Nat))
             -> snd Nat (forall (x : Nat) -> Nat) p
                  (fst Nat (forall (x : Nat) -> Nat) p))
             (pair Nat (forall (x : Nat) -> Nat) 3
               (fun (x : Nat) -> succ (succ x))))
        (fun (A : Type@0)
             (B : Type@0)
          -> forall (C : Type@0)
                    (pair : forall (a : A)
                                   (b : B)
                              -> C)
               -> C)
        (fun (A : Type@0)
             (B : Type@0)
             (a : A)
             (b : B)
             (C : Type@0)
             (pair : forall (a : A)
                            (b : B)
                       -> C)
          -> pair a b)
        (fun (A : Type@0)
             (B : Type@0)
             (p : forall (C : Type@0)
                         (pair : forall (a : A)
                                        (b : B)
                                   -> C)
                    -> C)
          -> p A (fun (a : A)
                      (b : B)
                   -> a))
        (fun (A : Type@0)
             (B : Type@0)
             (p : forall (C : Type@0)
                         (pair : forall (a : A)
                                        (b : B)
                                   -> C)
                    -> C)
          -> p B (fun (a : A)
                      (b : B)
                   -> b))
      : Nat
    Elaborated:
      (fun (x1 : forall (A1 : Type@0)
                        (A2 : Type@0)
                   -> Type@1)
           (x2 : forall (A3 : Type@0)
                        (A4 : Type@0)
                        (x3 : A3)
                        (x4 : A4)
                   -> x1 A3 A4)
           (x5 : forall (A5 : Type@0)
                        (A6 : Type@0)
                        (x6 : x1 A5 A6)
                   -> A5)
           (x7 : forall (A7 : Type@0)
                        (A8 : Type@0)
                        (x8 : x1 A7 A8)
                   -> A8)
        -> (fun (x9 : x1 Nat (forall (x10 : Nat) -> Nat))
             -> x7 Nat (forall (x11 : Nat) -> Nat) x9
                  (x5 Nat (forall (x12 : Nat) -> Nat) x9))
             (x2 Nat (forall (x13 : Nat) -> Nat) 3
               (fun (x14 : Nat) -> succ (succ x14))))
        (fun (A9 : Type@0)
             (A10 : Type@0)
          -> forall (A11 : Type@0)
                    (x15 : forall (x16 : A9)
                                  (x17 : A10)
                             -> A11)
               -> A11)
        (fun (A12 : Type@0)
             (A13 : Type@0)
             (x18 : A12)
             (x19 : A13)
             (A14 : Type@0)
             (x20 : forall (x21 : A12)
                           (x22 : A13)
                      -> A14)
          -> x20 x18 x19)
        (fun (A15 : Type@0)
             (A16 : Type@0)
             (x23 : forall (A17 : Type@0)
                           (x24 : forall (x25 : A15)
                                         (x26 : A16)
                                    -> A17)
                      -> A17)
          -> x23 A15 (fun (x27 : A15)
                          (x28 : A16)
                       -> x27))
        (fun (A18 : Type@0)
             (A19 : Type@0)
             (x29 : forall (A20 : Type@0)
                           (x30 : forall (x31 : A18)
                                         (x32 : A19)
                                    -> A20)
                      -> A20)
          -> x29 A19 (fun (x33 : A18)
                          (x34 : A19)
                       -> x34))
      : Nat
    Normalized Result:
      5 : Nat
  |}]

let%expect_test "vector.mctt works" =
  let _ = main_of_example "vector.mctt" in
  [%expect
    {|
    Parsed:
      (fun (Vec : forall (A : Type@0)
                         (n : Nat)
                    -> Type@2)
           (nil : forall (A : Type@0) -> Vec A 0)
           (cons : forall (A : Type@0)
                          (n : Nat)
                          (head : A)
                          (tail : Vec A n)
                     -> Vec A (succ n))
           (vecRec : forall (A : Type@0)
                            (n : Nat)
                            (vec : Vec A n)
                            (C : forall (l : Nat) -> Type@1)
                            (nil : C 0)
                            (cons : forall (l : Nat)
                                           (a : A)
                                           (r : C l)
                                      -> C (succ l))
                       -> C n)
        -> (fun (totalHead : forall (A : Type@0)
                                    (n : Nat)
                                    (vec : Vec A (succ n))
                               -> A)
                (vec : Vec (forall (n : Nat) -> Nat) 3)
             -> totalHead (forall (n : Nat) -> Nat) 2 vec 4)
             (fun (A : Type@0)
                  (n : Nat)
                  (vec : Vec A (succ n))
               -> vecRec A (succ n) vec
                    (fun (l : Nat)
                      -> rec l return r . Type@0
                         | zero => Nat
                         | succ l, r => A
                         end)
                    0
                    (fun (l : Nat)
                         (a : A)
                         (r : rec l return r . Type@0
                              | zero => Nat
                              | succ l, r => A
                              end)
                      -> a))
             (cons (forall (n : Nat) -> Nat) 2
                (fun (n : Nat) -> succ (succ (succ n)))
               (cons (forall (n : Nat) -> Nat) 1 (fun (n : Nat) -> succ n)
                 (cons (forall (n : Nat) -> Nat) 0
                    (fun (n : Nat) -> succ (succ n))
                   (nil (forall (n : Nat) -> Nat))))))
        (fun (A : Type@0)
             (n : Nat)
          -> forall (C : forall (l : Nat) -> Type@1)
                    (nil : C 0)
                    (cons : forall (l : Nat)
                                   (a : A)
                                   (r : C l)
                              -> C (succ l))
               -> C n)
        (fun (A : Type@0)
             (C : forall (l : Nat) -> Type@1)
             (nil : C 0)
             (cons : forall (l : Nat)
                            (a : A)
                            (r : C l)
                       -> C (succ l))
          -> nil)
        (fun (A : Type@0)
             (n : Nat)
             (head : A)
             (tail : forall (C : forall (l : Nat) -> Type@1)
                            (nil : C 0)
                            (cons : forall (l : Nat)
                                           (a : A)
                                           (r : C l)
                                      -> C (succ l))
                       -> C n)
             (C : forall (l : Nat) -> Type@1)
             (nil : C 0)
             (cons : forall (l : Nat)
                            (a : A)
                            (r : C l)
                       -> C (succ l))
          -> cons n head (tail C nil cons))
        (fun (A : Type@0)
             (n : Nat)
             (vec : forall (C : forall (l : Nat) -> Type@1)
                           (nil : C 0)
                           (cons : forall (l : Nat)
                                          (a : A)
                                          (r : C l)
                                     -> C (succ l))
                      -> C n)
             (C : forall (l : Nat) -> Type@1)
             (nil : C 0)
             (cons : forall (l : Nat)
                            (a : A)
                            (r : C l)
                       -> C (succ l))
          -> vec C nil cons)
      : Nat
    Elaborated:
      (fun (x1 : forall (A1 : Type@0)
                        (x2 : Nat)
                   -> Type@2)
           (x3 : forall (A2 : Type@0) -> x1 A2 0)
           (x4 : forall (A3 : Type@0)
                        (x5 : Nat)
                        (x6 : A3)
                        (x7 : x1 A3 x5)
                   -> x1 A3 (succ x5))
           (x8 : forall (A4 : Type@0)
                        (x9 : Nat)
                        (x10 : x1 A4 x9)
                        (x11 : forall (x12 : Nat) -> Type@1)
                        (x13 : x11 0)
                        (x14 : forall (x15 : Nat)
                                      (x16 : A4)
                                      (x17 : x11 x15)
                                 -> x11 (succ x15))
                   -> x11 x9)
        -> (fun (x18 : forall (A5 : Type@0)
                              (x19 : Nat)
                              (x20 : x1 A5 (succ x19))
                         -> A5)
                (x21 : x1 (forall (x22 : Nat) -> Nat) 3)
             -> x18 (forall (x23 : Nat) -> Nat) 2 x21 4)
             (fun (A6 : Type@0)
                  (x24 : Nat)
                  (x25 : x1 A6 (succ x24))
               -> x8 A6 (succ x24) x25
                    (fun (x26 : Nat)
                      -> rec x26 return x27 . Type@0
                         | zero => Nat
                         | succ x28, A7 => A6
                         end)
                    0
                    (fun (x29 : Nat)
                         (x30 : A6)
                         (x31 : rec x29 return x32 . Type@0
                                | zero => Nat
                                | succ x33, A8 => A6
                                end)
                      -> x30))
             (x4 (forall (x34 : Nat) -> Nat) 2
                (fun (x35 : Nat) -> succ (succ (succ x35)))
               (x4 (forall (x36 : Nat) -> Nat) 1 (fun (x37 : Nat) -> succ x37)
                 (x4 (forall (x38 : Nat) -> Nat) 0
                    (fun (x39 : Nat) -> succ (succ x39))
                   (x3 (forall (x40 : Nat) -> Nat))))))
        (fun (A9 : Type@0)
             (x41 : Nat)
          -> forall (x42 : forall (x43 : Nat) -> Type@1)
                    (x44 : x42 0)
                    (x45 : forall (x46 : Nat)
                                  (x47 : A9)
                                  (x48 : x42 x46)
                             -> x42 (succ x46))
               -> x42 x41)
        (fun (A10 : Type@0)
             (x49 : forall (x50 : Nat) -> Type@1)
             (x51 : x49 0)
             (x52 : forall (x53 : Nat)
                           (x54 : A10)
                           (x55 : x49 x53)
                      -> x49 (succ x53))
          -> x51)
        (fun (A11 : Type@0)
             (x56 : Nat)
             (x57 : A11)
             (x58 : forall (x59 : forall (x60 : Nat) -> Type@1)
                           (x61 : x59 0)
                           (x62 : forall (x63 : Nat)
                                         (x64 : A11)
                                         (x65 : x59 x63)
                                    -> x59 (succ x63))
                      -> x59 x56)
             (x66 : forall (x67 : Nat) -> Type@1)
             (x68 : x66 0)
             (x69 : forall (x70 : Nat)
                           (x71 : A11)
                           (x72 : x66 x70)
                      -> x66 (succ x70))
          -> x69 x56 x57 (x58 x66 x68 x69))
        (fun (A12 : Type@0)
             (x73 : Nat)
             (x74 : forall (x75 : forall (x76 : Nat) -> Type@1)
                           (x77 : x75 0)
                           (x78 : forall (x79 : Nat)
                                         (x80 : A12)
                                         (x81 : x75 x79)
                                    -> x75 (succ x79))
                      -> x75 x73)
             (x82 : forall (x83 : Nat) -> Type@1)
             (x84 : x82 0)
             (x85 : forall (x86 : Nat)
                           (x87 : A12)
                           (x88 : x82 x86)
                      -> x82 (succ x86))
          -> x74 x82 x84 x85)
      : Nat
    Normalized Result:
      7 : Nat
  |}]

let%expect_test "nary.mctt works" =
  let _ = main_of_example "nary.mctt" in
  [%expect
    {|
    Parsed:
      (fun (Nary : forall (n : Nat) -> Type@0)
           (toNat : forall (f : Nary 0) -> Nat)
           (appNary : forall (n : Nat)
                             (f : Nary (succ n))
                             (arg : Nat)
                        -> Nary n)
           (n : Nat)
           (f : Nary n)
        -> (rec n return y . forall (g : Nary y) -> Nat
            | zero => toNat
            | succ m, r => fun (g : Nary (succ m)) -> r (appNary m g (succ m))
            end)
             f)
        (fun (n : Nat)
          -> rec n return y . Type@0
             | zero => Nat
             | succ m, r => forall (a : Nat) -> r
             end)
        (fun (f : Nat) -> f)
        (fun (n : Nat)
             (f : rec succ n return y . Type@0
                  | zero => Nat
                  | succ m, r => forall (a : Nat) -> r
                  end)
             (arg : Nat)
          -> f arg)
        3
        ((fun (add : forall (a : Nat)
                            (b : Nat)
                       -> Nat)
              (a : Nat)
              (b : Nat)
              (c : Nat)
           -> add a (add b c))
          (fun (a : Nat)
               (b : Nat)
            -> rec a return y . Nat | zero => b | succ m, r => succ r end))
      : Nat
    Elaborated:
      (fun (x1 : forall (x2 : Nat) -> Type@0)
           (x3 : forall (x4 : x1 0) -> Nat)
           (x5 : forall (x6 : Nat)
                        (x7 : x1 (succ x6))
                        (x8 : Nat)
                   -> x1 x6)
           (x9 : Nat)
           (x10 : x1 x9)
        -> (rec x9 return x11 . forall (x14 : x1 x11) -> Nat
            | zero => x3
            | succ x12, x13 =>
              fun (x15 : x1 (succ x12)) -> x13 (x5 x12 x15 (succ x12))
            end)
             x10)
        (fun (x16 : Nat)
          -> rec x16 return x17 . Type@0
             | zero => Nat
             | succ x18, A1 => forall (x19 : Nat) -> A1
             end)
        (fun (x20 : Nat) -> x20)
        (fun (x21 : Nat)
             (x22 : rec succ x21 return x23 . Type@0
                    | zero => Nat
                    | succ x24, A2 => forall (x25 : Nat) -> A2
                    end)
             (x26 : Nat)
          -> x22 x26)
        3
        ((fun (x27 : forall (x28 : Nat)
                            (x29 : Nat)
                       -> Nat)
              (x30 : Nat)
              (x31 : Nat)
              (x32 : Nat)
           -> x27 x30 (x27 x31 x32))
          (fun (x33 : Nat)
               (x34 : Nat)
            -> rec x33 return x35 . Nat
               | zero => x34
               | succ x36, x37 => succ x37
               end))
      : Nat
    Normalized Result:
      6 : Nat
  |}]

let%expect_test "simple_let.mctt works" =
  let _ = main_of_example "simple_let.mctt" in
  [%expect
    {| 
      Parsed:
        (fun (x : Nat) -> succ x) 0 : Nat
      Elaborated:
        (fun (x1 : Nat) -> succ x1) 0 : Nat
      Normalized Result:
        1 : Nat      
  |}]

let%expect_test "let_two_vars.mctt works" =
  let _ = main_of_example "let_two_vars.mctt" in
  [%expect
     {|
       Parsed:
         (fun (x : Nat)
              (f : forall (y : Nat) -> Nat)
           -> f x) 0 (fun (n : Nat) -> n)
         : Nat
       Elaborated:
         (fun (x1 : Nat)
              (x2 : forall (x3 : Nat) -> Nat)
           -> x2 x1) 0
           (fun (x4 : Nat) -> x4)
         : Nat
       Normalized Result:
         0 : Nat
  |}]

let%expect_test "let_nary.mctt works" =
  let _ = main_of_example "let_nary.mctt" in
  [%expect
     {|
       Parsed:
         (fun (Nary : forall (n : Nat) -> Type@0)
              (toNat : forall (f : Nary 0) -> Nat)
              (appNary : forall (n : Nat)
                                (f : Nary (succ n))
                                (arg : Nat)
                           -> Nary n)
              (n : Nat)
              (f : Nary n)
           -> (rec n return y . forall (g : Nary y) -> Nat
               | zero => toNat
               | succ m, r => fun (g : Nary (succ m)) -> r (appNary m g (succ m))
               end)
                f)
           (fun (n : Nat)
             -> rec n return y . Type@0
                | zero => Nat
                | succ m, r => forall (a : Nat) -> r
                end)
           (fun (f : Nat) -> f)
           (fun (n : Nat)
                (f : rec succ n return y . Type@0
                     | zero => Nat
                     | succ m, r => forall (a : Nat) -> r
                     end)
                (arg : Nat)
             -> f arg)
           3
           ((fun (add : forall (a : Nat)
                               (b : Nat)
                          -> Nat)
                 (a : Nat)
                 (b : Nat)
                 (c : Nat)
              -> add a (add b c))
             (fun (a : Nat)
                  (b : Nat)
               -> rec a return y . Nat | zero => b | succ m, r => succ r end))
         : Nat
       Elaborated:
         (fun (x1 : forall (x2 : Nat) -> Type@0)
              (x3 : forall (x4 : x1 0) -> Nat)
              (x5 : forall (x6 : Nat)
                           (x7 : x1 (succ x6))
                           (x8 : Nat)
                      -> x1 x6)
              (x9 : Nat)
              (x10 : x1 x9)
           -> (rec x9 return x11 . forall (x14 : x1 x11) -> Nat
               | zero => x3
               | succ x12, x13 =>
                 fun (x15 : x1 (succ x12)) -> x13 (x5 x12 x15 (succ x12))
               end)
                x10)
           (fun (x16 : Nat)
             -> rec x16 return x17 . Type@0
                | zero => Nat
                | succ x18, A1 => forall (x19 : Nat) -> A1
                end)
           (fun (x20 : Nat) -> x20)
           (fun (x21 : Nat)
                (x22 : rec succ x21 return x23 . Type@0
                       | zero => Nat
                       | succ x24, A2 => forall (x25 : Nat) -> A2
                       end)
                (x26 : Nat)
             -> x22 x26)
           3
           ((fun (x27 : forall (x28 : Nat)
                               (x29 : Nat)
                          -> Nat)
                 (x30 : Nat)
                 (x31 : Nat)
                 (x32 : Nat)
              -> x27 x30 (x27 x31 x32))
             (fun (x33 : Nat)
                  (x34 : Nat)
               -> rec x33 return x35 . Nat
                  | zero => x34
                  | succ x36, x37 => succ x37
                  end))
         : Nat
       Normalized Result:
         6 : Nat
  |}]


let%expect_test "let_vector.mctt works" =
  let _ = main_of_example "let_vector.mctt" in
  [%expect
    {| 
      Parsed:
        (fun (Vec : forall (A : Type@0)
                           (n : Nat)
                      -> Type@2)
             (nil : forall (A : Type@0) -> Vec A 0)
             (cons : forall (A : Type@0)
                            (n : Nat)
                            (head : A)
                            (tail : Vec A n)
                       -> Vec A (succ n))
             (vecRec : forall (A : Type@0)
                              (n : Nat)
                              (vec : Vec A n)
                              (C : forall (l : Nat) -> Type@1)
                              (nil : C 0)
                              (cons : forall (l : Nat)
                                             (a : A)
                                             (r : C l)
                                        -> C (succ l))
                         -> C n)
          -> (fun (totalHead : forall (A : Type@0)
                                      (n : Nat)
                                      (vec : Vec A (succ n))
                                 -> A)
                  (vec : Vec (forall (n : Nat) -> Nat) 3)
               -> totalHead (forall (n : Nat) -> Nat) 2 vec 4)
               (fun (A : Type@0)
                    (n : Nat)
                    (vec : Vec A (succ n))
                 -> vecRec A (succ n) vec
                      (fun (l : Nat)
                        -> rec l return r . Type@0
                           | zero => Nat
                           | succ l, r => A
                           end)
                      0
                      (fun (l : Nat)
                           (a : A)
                           (r : rec l return r . Type@0
                                | zero => Nat
                                | succ l, r => A
                                end)
                        -> a))
               (cons (forall (n : Nat) -> Nat) 2
                  (fun (n : Nat) -> succ (succ (succ n)))
                 (cons (forall (n : Nat) -> Nat) 1 (fun (n : Nat) -> succ n)
                   (cons (forall (n : Nat) -> Nat) 0
                      (fun (n : Nat) -> succ (succ n))
                     (nil (forall (n : Nat) -> Nat))))))
          (fun (A : Type@0)
               (n : Nat)
            -> forall (C : forall (l : Nat) -> Type@1)
                      (nil : C 0)
                      (cons : forall (l : Nat)
                                     (a : A)
                                     (r : C l)
                                -> C (succ l))
                 -> C n)
          (fun (A : Type@0)
               (C : forall (l : Nat) -> Type@1)
               (nil : C 0)
               (cons : forall (l : Nat)
                              (a : A)
                              (r : C l)
                         -> C (succ l))
            -> nil)
          (fun (A : Type@0)
               (n : Nat)
               (head : A)
               (tail : forall (C : forall (l : Nat) -> Type@1)
                              (nil : C 0)
                              (cons : forall (l : Nat)
                                             (a : A)
                                             (r : C l)
                                        -> C (succ l))
                         -> C n)
               (C : forall (l : Nat) -> Type@1)
               (nil : C 0)
               (cons : forall (l : Nat)
                              (a : A)
                              (r : C l)
                         -> C (succ l))
            -> cons n head (tail C nil cons))
          (fun (A : Type@0)
               (n : Nat)
               (vec : forall (C : forall (l : Nat) -> Type@1)
                             (nil : C 0)
                             (cons : forall (l : Nat)
                                            (a : A)
                                            (r : C l)
                                       -> C (succ l))
                        -> C n)
               (C : forall (l : Nat) -> Type@1)
               (nil : C 0)
               (cons : forall (l : Nat)
                              (a : A)
                              (r : C l)
                         -> C (succ l))
            -> vec C nil cons)
        : Nat
      Elaborated:
        (fun (x1 : forall (A1 : Type@0)
                          (x2 : Nat)
                     -> Type@2)
             (x3 : forall (A2 : Type@0) -> x1 A2 0)
             (x4 : forall (A3 : Type@0)
                          (x5 : Nat)
                          (x6 : A3)
                          (x7 : x1 A3 x5)
                     -> x1 A3 (succ x5))
             (x8 : forall (A4 : Type@0)
                          (x9 : Nat)
                          (x10 : x1 A4 x9)
                          (x11 : forall (x12 : Nat) -> Type@1)
                          (x13 : x11 0)
                          (x14 : forall (x15 : Nat)
                                        (x16 : A4)
                                        (x17 : x11 x15)
                                   -> x11 (succ x15))
                     -> x11 x9)
          -> (fun (x18 : forall (A5 : Type@0)
                                (x19 : Nat)
                                (x20 : x1 A5 (succ x19))
                           -> A5)
                  (x21 : x1 (forall (x22 : Nat) -> Nat) 3)
               -> x18 (forall (x23 : Nat) -> Nat) 2 x21 4)
               (fun (A6 : Type@0)
                    (x24 : Nat)
                    (x25 : x1 A6 (succ x24))
                 -> x8 A6 (succ x24) x25
                      (fun (x26 : Nat)
                        -> rec x26 return x27 . Type@0
                           | zero => Nat
                           | succ x28, A7 => A6
                           end)
                      0
                      (fun (x29 : Nat)
                           (x30 : A6)
                           (x31 : rec x29 return x32 . Type@0
                                  | zero => Nat
                                  | succ x33, A8 => A6
                                  end)
                        -> x30))
               (x4 (forall (x34 : Nat) -> Nat) 2
                  (fun (x35 : Nat) -> succ (succ (succ x35)))
                 (x4 (forall (x36 : Nat) -> Nat) 1 (fun (x37 : Nat) -> succ x37)
                   (x4 (forall (x38 : Nat) -> Nat) 0
                      (fun (x39 : Nat) -> succ (succ x39))
                     (x3 (forall (x40 : Nat) -> Nat))))))
          (fun (A9 : Type@0)
               (x41 : Nat)
            -> forall (x42 : forall (x43 : Nat) -> Type@1)
                      (x44 : x42 0)
                      (x45 : forall (x46 : Nat)
                                    (x47 : A9)
                                    (x48 : x42 x46)
                               -> x42 (succ x46))
                 -> x42 x41)
          (fun (A10 : Type@0)
               (x49 : forall (x50 : Nat) -> Type@1)
               (x51 : x49 0)
               (x52 : forall (x53 : Nat)
                             (x54 : A10)
                             (x55 : x49 x53)
                        -> x49 (succ x53))
            -> x51)
          (fun (A11 : Type@0)
               (x56 : Nat)
               (x57 : A11)
               (x58 : forall (x59 : forall (x60 : Nat) -> Type@1)
                             (x61 : x59 0)
                             (x62 : forall (x63 : Nat)
                                           (x64 : A11)
                                           (x65 : x59 x63)
                                      -> x59 (succ x63))
                        -> x59 x56)
               (x66 : forall (x67 : Nat) -> Type@1)
               (x68 : x66 0)
               (x69 : forall (x70 : Nat)
                             (x71 : A11)
                             (x72 : x66 x70)
                        -> x66 (succ x70))
            -> x69 x56 x57 (x58 x66 x68 x69))
          (fun (A12 : Type@0)
               (x73 : Nat)
               (x74 : forall (x75 : forall (x76 : Nat) -> Type@1)
                             (x77 : x75 0)
                             (x78 : forall (x79 : Nat)
                                           (x80 : A12)
                                           (x81 : x75 x79)
                                      -> x75 (succ x79))
                        -> x75 x73)
               (x82 : forall (x83 : Nat) -> Type@1)
               (x84 : x82 0)
               (x85 : forall (x86 : Nat)
                             (x87 : A12)
                             (x88 : x82 x86)
                        -> x82 (succ x86))
            -> x74 x82 x84 x85)
        : Nat
      Normalized Result:
        7 : Nat
  |}]


(* let%test "lambda" = *)
(*   parse "fun (x : Type 5).y" = Some (Coq_fn (x, Coq_typ 5, Coq_var y)) *)

(* let%test "lambda multiple args" = *)
(*   parse "fun (x : Nat) (y : Nat) . x" *)
(*   = Some (Coq_fn (x, Coq_nat, Coq_fn (y, Coq_nat, Coq_var x))) *)

(* let%test "lambda multiple args 2" = *)
(*   parse "fun (x : Nat) (y : Nat) (z : Nat) . z" *)
(*   = Some *)
(*       (Coq_fn (x, Coq_nat, Coq_fn (y, Coq_nat, Coq_fn (z, Coq_nat, Coq_var z)))) *)

(* let%test "application" = *)
(*   parse "(fun (x : Nat).x) Nat" *)
(*   = Some (Coq_app (Coq_fn (x, Coq_nat, Coq_var x), Coq_nat)) *)

(* let%test "nested 1" = *)
(*   parse "(Type 5) zero" = Some (Coq_app (Coq_typ 5, Coq_zero)) *)

(* let%test "nested 2" = *)
(*   parse "succ (succ (succ (succ zero)))" *)
(*   = Some (Coq_succ (Coq_succ (Coq_succ (Coq_succ Coq_zero)))) *)

(* let%test "pi" = parse "pi (x:Nat).x" = Some (Coq_pi (x, Coq_nat, Coq_var x)) *)

(* let%test "pi multiple args" = *)
(*   parse "pi (x : Nat) (y : Nat) (z : Nat) . z" *)
(*   = Some *)
(*       (Coq_pi (x, Coq_nat, Coq_pi (y, Coq_nat, Coq_pi (z, Coq_nat, Coq_var z)))) *)

(* (\* Some more finer details *\) *)

(* let%test "pi missing colon" = parse "pi (x Nat).x" = None *)

(* let%test "ignore whitespace" = *)
(*   parse "fun (x  \n                                     : Type 4).x" *)
(*   = Some (Coq_fn (x, Coq_typ 4, Coq_var x)) *)
