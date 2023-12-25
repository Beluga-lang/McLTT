Require Extraction.
Require Import Frontend.Parser.

Import MenhirLibParser.Inter.
Extraction Language OCaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.

Extraction "parser.ml" Parser.prog.
