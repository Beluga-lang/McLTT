(lang dune 3.4)
(using menhir 2.1)

(generate_opam_files)

(package
 (name mcltt)
 (synopsis "A Bottom-up Approach to Implementing A Proof Assistant")
 (depends ppx_inline_test))
