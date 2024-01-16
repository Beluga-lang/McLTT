From Coq Require Extraction.

From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlNatInt.
From Coq Require Import ExtrOcamlNativeString.

From Mcltt Require Import Parser.
Import MenhirLibParser.Inter.

Extraction Language OCaml.

Extraction "parser.ml" Parser.prog.
