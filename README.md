# McLTT: A Bottom-up Approach to Implementing A Proof Assistant

In McLTT, we build a verified, runnable typechecker for Martin-Löf type theory. After
the accomplishment of this project, we will obtain an executable, to which we can feed
a program in Martin-Loef type theory, and this executable will check whether this
program has the specified type. McLTT is novel in that it is implemented in
Coq. Moreover, we will prove that the typechecking algorithm extracted from Coq is
sound and complete: a program passes typechecking if and only if it is a well-typed
program in MLTT. This will be the first verified proof assistant (despite being
elementary) and serves as a basis for future extensions. 


## Architecture

McLTT has the following architecture:

```
    | source code of McLTT
    v
+-------+
| lexer |          OCaml code generated by ocamllex
+-------+
    | stream of tokens
    v
+--------+
| parser |         Coq code generated by Menhir
+--------+
    | concrete syntax tree
    v
+------------+
| elaborator |     Coq code
+------------+
    | abstract syntax tree
    v
+-------------+
| typechecker |    Coq code
| (normalizer |
|   included) |
+-------------+
    | yes or no    Driver in OCaml
    v
```

In this architecture, most code is in Coq, with accompanying theorems to justify the
implementation. 


## Dependencies

* OCaml 4.14.0
* Menhir
* coq-menhirlib
* Coq 8.16.1
* Equations 1.3

We recommend to install dependencies in the following way:

```bash
opam switch add coq-8.16.1 4.14.0
opam pin add coq 8.16.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations
opam install coq-menhirlib
```
