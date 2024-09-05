module Parser = MclttExtracted.Parser
module Entrypoint = MclttExtracted.Entrypoint
open Parser
open MenhirLibParser.Inter
open Entrypoint

let parse text =
  (* Before parsing, we must generate a token stream from a lexer buffer,
     which we then feed into the parser. *)
  let rec loop lexbuf = lazy (Buf_cons (Lexer.read lexbuf, loop lexbuf)) in
  let token_stream = loop (Lexing.from_string text) in
  match Parser.prog 50 token_stream with
  | Parsed_pr ((exp, _typ), _) -> Some exp
  | Fail_pr_full (_, _) -> None
  | _ -> None

let main () =
  print_string "File path to load: ";
  let fp = read_line () in
  let chan = open_in fp in
  (* Before parsing, we must generate a token stream from a lexer buffer,
     which we then feed into the parser. *)
  let rec loop lexbuf = lazy (Buf_cons (Lexer.read lexbuf, loop lexbuf)) in
  let token_stream = loop (Lexing.from_channel chan) in
  Entrypoint.main 50 token_stream
