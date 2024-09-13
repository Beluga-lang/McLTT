module Parser = MclttExtracted.Parser
module Entrypoint = MclttExtracted.Entrypoint
open Parser
open MenhirLibParser.Inter
open Entrypoint

let main filename =
  Lexing.from_channel (open_in filename)
  |> Lexer.lexbuf_to_token_buffer
  (* Here, the integer argument is a *log* version of fuel.
     Thus, 500 means 2^500. *)
  |> Entrypoint.main 500
  |> Format.printf "%a@." PrettyPrinter.format_main_result
