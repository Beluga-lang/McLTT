open Parser.MenhirLibParser.Inter

let rec loop x = lazy (Buf_cons (Lexer.read x, loop x))

let parse s =
  let lexbuf = Lexing.from_string s in
  let buffer = loop lexbuf in
  match Parser.prog 50 buffer with
  | Parsed_pr (e, _) -> Some e
  | Fail_pr_full (_, _) -> None
  | _ -> None

