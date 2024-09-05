{
  open Lexing
  open MclttExtracted.Parser

  let get_position lexbuf = (lexbuf.lex_start_p, lexbuf.lex_curr_p)
}

let string = ['a'-'z''A'-'Z']+

rule read =
  parse
  | "->" { ARROW (get_position lexbuf) }
  | '@' { AT (get_position lexbuf) }
  | '|' { BAR (get_position lexbuf) }
  | ':' { COLON (get_position lexbuf) }
  | ',' { COMMA (get_position lexbuf) }
  | "=>" { DARROW (get_position lexbuf) }
  | "(*" { comment lexbuf }
  | '(' { LPAREN (get_position lexbuf) }
  | ')' { RPAREN (get_position lexbuf) }
  | "zero" { ZERO (get_position lexbuf) }
  | "succ" { SUCC (get_position lexbuf) }
  | "rec" { REC (get_position lexbuf) }
  | "return" { RETURN (get_position lexbuf) }
  | "end" { END (get_position lexbuf) }
  | "fun" { LAMBDA (get_position lexbuf) }
  | "forall" { PI (get_position lexbuf) }
  | [' ' '\t'] { read lexbuf }
  | ['\n'] { new_line lexbuf; read lexbuf }
  | "Nat" { NAT (get_position lexbuf) }
  | ['0'-'9']+ as lxm { INT (get_position lexbuf, int_of_string lxm) }
  | "Type" { TYPE (get_position lexbuf) }
  | string { VAR (get_position lexbuf, Lexing.lexeme lexbuf) }
  | eof { EOF (get_position lexbuf) }
  | _ as c { failwith (Printf.sprintf "unexpected character: %C at line %d, column %d" c lexbuf.lex_start_p.pos_lnum (lexbuf.lex_start_p.pos_cnum - lexbuf.lex_start_p.pos_bol)) }
and comment =
  parse
  | "*)" { read lexbuf }
  | _ { comment lexbuf }
