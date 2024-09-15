module Parser = MclttExtracted.Parser
module Entrypoint = MclttExtracted.Entrypoint
open Parser
open MenhirLibParser.Inter
open Entrypoint

let get_exit_code result : int =
  match result with
  | AllGood _ -> 0
  | TypeCheckingFailure _ -> 1
  | ElaborationFailure _ -> 2
  | ParserFailure _ -> 3
  | ParserTimeout _ -> 4

let main_of_lexbuf lexbuf =
  Lexer.lexbuf_to_token_buffer lexbuf
  (* Here, the integer argument is a *log* version of fuel.
     Thus, 500 means 2^500. *)
  |> Entrypoint.main 500
  |> fun r -> Format.printf "%a@." PrettyPrinter.format_main_result r; get_exit_code r

let main_of_filename filename =
  Lexing.from_channel (open_in filename) |> main_of_lexbuf

let main_of_program_string program =
  Lexing.from_string program |> main_of_lexbuf
