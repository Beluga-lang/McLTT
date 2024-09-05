{
  open Lexing
  open MclttExtracted.Parser

  let get_range lexbuf = (lexbuf.lex_start_p, lexbuf.lex_curr_p)

  let format_position (f: Format.formatter) (p: position): unit =
    Format.fprintf
      f
      "line %d, column %d"
      p.pos_lnum
      (p.pos_cnum - p.pos_bol + 1)

  let format_range (f: Format.formatter) (p: position * position): unit =
    Format.fprintf
      f
      "@[<h>%a - %a@]"
      format_position (fst p)
      format_position (snd p)
}

let string = ['a'-'z''A'-'Z']+

rule read =
  parse
  | "->" { ARROW (get_range lexbuf) }
  | '@' { AT (get_range lexbuf) }
  | '|' { BAR (get_range lexbuf) }
  | ':' { COLON (get_range lexbuf) }
  | ',' { COMMA (get_range lexbuf) }
  | "=>" { DARROW (get_range lexbuf) }
  | "(*" { comment lexbuf }
  | '(' { LPAREN (get_range lexbuf) }
  | ')' { RPAREN (get_range lexbuf) }
  | "zero" { ZERO (get_range lexbuf) }
  | "succ" { SUCC (get_range lexbuf) }
  | "rec" { REC (get_range lexbuf) }
  | "return" { RETURN (get_range lexbuf) }
  | "end" { END (get_range lexbuf) }
  | "fun" { LAMBDA (get_range lexbuf) }
  | "forall" { PI (get_range lexbuf) }
  | [' ' '\t'] { read lexbuf }
  | ['\n'] { new_line lexbuf; read lexbuf }
  | "Nat" { NAT (get_range lexbuf) }
  | ['0'-'9']+ as lxm { INT (get_range lexbuf, int_of_string lxm) }
  | "Type" { TYPE (get_range lexbuf) }
  | string { VAR (get_range lexbuf, Lexing.lexeme lexbuf) }
  | eof { EOF (get_range lexbuf) }
  | _ as c { failwith (Format.asprintf "@[<v 2>Lexer error:@ @[<v 2>Unexpected character %C@ at %a@]@]@." c format_position lexbuf.lex_start_p) }
and comment =
  parse
  | "*)" { read lexbuf }
  | _ { comment lexbuf }
