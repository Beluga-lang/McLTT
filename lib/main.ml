open Cst

let parse (s : string) : obj =
  let lexbuf = Lexing.from_string s in
  let cst = Parser.prog Lexer.read lexbuf in
  cst


