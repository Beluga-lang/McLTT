module Parser = MclttExtracted.Parser
module Entrypoint = MclttExtracted.Entrypoint
open Parser
open MenhirLibParser.Inter
open Entrypoint

let main_of_lexbuf lexbuf =
  Lexer.lexbuf_to_token_buffer lexbuf
  (* Here, the integer argument is a *log* version of fuel.
     Thus, 500 means 2^500. *)
  |> Entrypoint.main 500
  |> Format.printf "%a@." PrettyPrinter.format_main_result

let main_of_filename filename =
  Lexing.from_channel (open_in filename) |> main_of_lexbuf

let main_of_program_string program =
  Lexing.from_string program |> main_of_lexbuf
