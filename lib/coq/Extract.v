(* Requires menhirlib: opam install coq-menhirlib *)

Require Extraction.
From McLtt Require Import Parser.

Import MenhirLibParser.Inter.
Extraction Language OCaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

(* Meant to be run in this directory *)
Extraction "../parser.ml" Parser.prog.
