module Parser = MclttExtracted.Parser
module Entrypoint = MclttExtracted.Entrypoint
open Parser
open MenhirLibParser.Inter
open Entrypoint

let main filename =
  open_in filename
  |> Lexing.from_channel
  (* Before parsing, we must generate a stream of tokens from a lexer buffer,
     which we then feed into the parser. *)
  |> Lexer.lexbuf_to_token_buffer
  |> Entrypoint.main 500
  |> Format.printf "%a@."
       PrettyPrinter.format_main_result
