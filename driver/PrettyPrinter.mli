val format_obj : Format.formatter -> MclttExtracted.Syntax.Cst.obj -> unit
val format_exp : Format.formatter -> MclttExtracted.Syntax.exp -> unit
val format_nf : Format.formatter -> MclttExtracted.Syntax.nf -> unit

val format_main_result :
  Format.formatter -> MclttExtracted.Entrypoint.main_result -> unit
