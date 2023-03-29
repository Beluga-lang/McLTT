open Parser.MenhirLibParser.Inter

let parse text =
  (* Before parsing, we must generate a token stream from a lexer buffer,
     which we then feed into the parser. *)
  let rec loop lexbuf = lazy (Buf_cons (Lexer.read lexbuf, loop lexbuf)) in
  let token_stream = loop (Lexing.from_string text) in
  match Parser.prog 50 token_stream with
  | Parsed_pr (e, _) -> Some e
  | Fail_pr_full (_, _) -> None
  | _ -> None
