{
  open Parser
}

let string = ['a'-'z']+

rule read =
  parse
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '.' { DOT }
  | ':' { COLON }
  | "zero" { ZERO }
  | "succ " { SUCC }
  | "fun" { LAMBDA }
  | [' ' '\t' '\n' ] { read lexbuf }
  | "Nat" { NAT }
  | ['0'-'9']+ as lxm { INT(int_of_string lxm) }
  | "Type" { TYPE }
  | string { VAR (Lexing.lexeme lexbuf) }
  | eof { EOF }
