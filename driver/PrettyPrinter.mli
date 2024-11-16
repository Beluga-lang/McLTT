val format_obj : Format.formatter -> McttExtracted.Syntax.Cst.obj -> unit
val format_exp : Format.formatter -> McttExtracted.Syntax.exp -> unit
val format_nf : Format.formatter -> McttExtracted.Syntax.nf -> unit

val format_main_result :
  Format.formatter -> McttExtracted.Entrypoint.main_result -> unit
