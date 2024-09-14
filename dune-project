(lang dune 3.13)
(using menhir 2.1)
(name mcltt)

(generate_opam_files)

(license MIT)
(authors "Antoine Gaulin"
         "Jason Hu"
         "Junyoung Jang")
(maintainers "the CompLogic group, McGill University")
(homepage "https://beluga-lang.github.io/McLTT/")
(documentation "https://beluga-lang.github.io/McLTT/")
(source (github Beluga-lang/McLTT))

(package
 (name mcltt)
 (synopsis "A Bottom-up Approach to Implementing A Proof Assistant")
 (description "In McLTT, we build a verified, runnable typechecker for Martin-Löf type theory. After
the accomplishment of this project, we will obtain an executable, to which we can feed
a program in Martin-Loef type theory, and this executable will check whether this
program has the specified type. McLTT is novel in that it is implemented in
Coq. Moreover, we will prove that the typechecking algorithm extracted from Coq is
sound and complete: a program passes typechecking if and only if it is a well-typed
program in MLTT. This will be the first verified proof assistant (despite being
elementary) and serves as a basis for future extensions.")
 (depends
  (ocaml (>= "4.14.2"))
  (coq   (= "8.20.0"))
  (menhir (= "20240715"))
  (coq-menhirlib (= "20240715"))
  (coq-equations (= "1.3.1+8.20"))
  (ppx_expect (>= "0.16.0"))
  (sherlodoc :with-doc)))
