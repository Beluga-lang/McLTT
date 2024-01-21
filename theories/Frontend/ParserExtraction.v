From Coq Require Extraction.

From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.

From Mcltt Require Import Parser.
Import MenhirLibParser.Inter.

Extraction Language OCaml.

Extraction "parser.ml" Parser.prog.
