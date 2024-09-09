module Parser = MclttExtracted.Parser
module Entrypoint = MclttExtracted.Entrypoint
open Parser
open MenhirLibParser.Inter
open Entrypoint

let main ?(default_fp = "") () =
  let fp =
    if default_fp <> ""
    then default_fp
    else
      begin
        print_string "File path to load: ";
        read_line ()
      end
  in
  let chan = open_in fp in
  (* Before parsing, we must generate a token stream from a lexer buffer,
     which we then feed into the parser. *)
  let rec loop lexbuf =
    lazy (
        try
          Buf_cons (Lexer.read lexbuf, loop lexbuf)
        with
        | Failure s -> prerr_string s; raise Exit) in
  let token_stream = loop (Lexing.from_channel chan) in
  let res = Entrypoint.main 500 token_stream in
  Format.printf "%a@."
    PrettyPrinter.format_main_result res
