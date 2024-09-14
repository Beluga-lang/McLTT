val format_position : Format.formatter -> Lexing.position -> unit
val format_range : Format.formatter -> Lexing.position * Lexing.position -> unit
val format_token : Format.formatter -> MclttExtracted.Parser.token -> unit
val read : Lexing.lexbuf -> MclttExtracted.Parser.token

val lexbuf_to_token_buffer :
  Lexing.lexbuf -> MclttExtracted.Parser.MenhirLibParser.Inter.buffer
