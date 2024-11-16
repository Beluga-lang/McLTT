val format_position : Format.formatter -> Lexing.position -> unit
val format_range : Format.formatter -> Lexing.position * Lexing.position -> unit
val format_token : Format.formatter -> McttExtracted.Parser.token -> unit
val read : Lexing.lexbuf -> McttExtracted.Parser.token

val lexbuf_to_token_buffer :
  Lexing.lexbuf -> McttExtracted.Parser.MenhirLibParser.Inter.buffer
