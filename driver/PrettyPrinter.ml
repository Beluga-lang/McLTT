open MclttExtracted.Entrypoint
open MclttExtracted.Syntax
module Parser = MclttExtracted.Parser
module ParserMessages = MclttExtracted.ParserMessages

(************************************************************)
(* Formatting helpers *)
(************************************************************)

let pp_print_paren_if
    (cond : bool)
    (body : Format.formatter -> unit -> unit)
    (f : Format.formatter)
    () : unit =
  if cond then Format.pp_print_char f '(';
  body f ();
  if cond then Format.pp_print_char f ')'

(************************************************************)
(* Formatting Cst.obj *)
(************************************************************)
let rec get_nat_of_obj : Cst.obj -> int option = function
  | Cst.Coq_zero -> Some 0
  | Cst.Coq_succ e -> Option.map (( + ) 1) (get_nat_of_obj e)
  | _ -> None

let rec get_fn_params_of_obj : Cst.obj -> (string * Cst.obj) list * Cst.obj =
  function
  | Cst.Coq_fn (px, ep, ebody) ->
     let params, ebody' = get_fn_params_of_obj ebody in
     ((px, ep) :: params, ebody')
  | ebody -> ([], ebody)

let rec get_pi_params_of_obj : Cst.obj -> (string * Cst.obj) list * Cst.obj =
  function
  | Cst.Coq_pi (px, ep, eret) ->
     let params, eret' = get_pi_params_of_obj eret in
     ((px, ep) :: params, eret')
  | eret -> ([], eret)

let rec format_obj_prec (p : int) (f : Format.formatter) : Cst.obj -> unit =
  let open Format in
  function
  | Cst.Coq_typ i -> fprintf f "Type@%d" i
  | Cst.Coq_nat -> fprintf f "Nat"
  | Cst.Coq_zero -> fprintf f "0"
  | Cst.Coq_succ e -> begin
     match get_nat_of_obj e with
     | Some n -> fprintf f "%d" (1 + n)
     | None ->
        let impl f () = fprintf f "succ@ %a" (format_obj_prec 2) e in
        pp_open_hovbox f 2;
        pp_print_paren_if (p >= 2) impl f ();
        pp_close_box f ()
   end
  | Cst.Coq_natrec (escr, mx, em, ez, sx, sr, es) ->
     let impl f () =
       fprintf f
         "@[<hv 0>@[<hov 2>rec %a@ return %s -> %a@]@ @[<hov 2>| zero =>@ \
          %a@]@ @[<hov 2>| succ %s, %s =>@ %a@]@ end@]"
         format_obj escr mx format_obj em format_obj ez sx sr format_obj es
     in
     pp_print_paren_if (p >= 1) impl f ()
  | Cst.Coq_app (ef, ea) ->
     let impl f () =
       fprintf f "%a@ %a" (format_obj_prec 1) ef (format_obj_prec 2) ea
     in
     pp_open_hvbox f 2;
     pp_print_paren_if (p >= 2) impl f ();
     pp_close_box f ()
  | Cst.Coq_fn (px, ep, ebody) ->
     let params, ebody' = get_fn_params_of_obj ebody in
     let impl f () =
       pp_print_string f "fun ";
       pp_open_tbox f ();
       pp_set_tab f ();
       pp_print_list ~pp_sep:pp_print_tab format_obj_param f ((px, ep) :: params);
       pp_close_tbox f ();
       begin
         if List.compare_length_with params 0 = 0
         then pp_print_space f ()
         else pp_force_newline f ()
       end;
       fprintf f "-> @[<hov 2>%a@]" format_obj ebody'
     in
     pp_open_hvbox f 2;
     pp_print_paren_if (p >= 1) impl f ();
     pp_close_box f ()
  | Cst.Coq_pi (px, ep, eret) ->
     let params, eret' = get_pi_params_of_obj eret in
     let impl f () =
       pp_print_string f "forall ";
       pp_open_tbox f ();
       pp_set_tab f ();
       pp_print_list ~pp_sep:pp_print_tab format_obj_param f ((px, ep) :: params);
       pp_close_tbox f ();
       begin
         if List.compare_length_with params 0 = 0
         then pp_print_space f ()
         else pp_force_newline f ()
       end;
       fprintf f "-> @[<hov 2>%a@]" format_obj eret'
     in
     pp_open_hvbox f 2;
     pp_print_paren_if (p >= 1) impl f ();
     pp_close_box f ()
  | Cst.Coq_var x -> pp_print_string f x

and format_obj_param f (px, ep) = Format.fprintf f "(%s : %a)" px format_obj ep
and format_obj f = format_obj_prec 0 f

(************************************************************)
(* Formatting exp *)
(************************************************************)
let exp_to_obj =
  let new_var, reset_var_suffix =
    let suffix = ref 0 in
    ( (fun () ->
        incr suffix;
        "x" ^ string_of_int !suffix),
      fun () -> suffix := 0 )
  in
  let new_tyvar, reset_tyvar_suffix =
    let suffix = ref 0 in
    ( (fun () ->
        incr suffix;
        "A" ^ string_of_int !suffix),
      fun () -> suffix := 0 )
  in
  let rec impl (ctx : string list) : exp -> Cst.obj = function
    | Coq_a_zero -> Cst.Coq_zero
    | Coq_a_succ e -> Cst.Coq_succ (impl ctx e)
    | Coq_a_natrec (em, ez, es, escr) ->
       let mx = new_var () in
       let sx = new_var () in
       let sr = match em with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let escr' = impl ctx escr in
       let em' = impl (mx :: ctx) em in
       let ez' = impl ctx ez in
       let es' = impl (sr :: sx :: ctx) es in
       Cst.Coq_natrec (escr', mx, em', ez', sx, sr, es')
    | Coq_a_nat -> Cst.Coq_nat
    | Coq_a_typ i -> Cst.Coq_typ i
    | Coq_a_var x -> Cst.Coq_var (List.nth ctx x)
    | Coq_a_fn (ep, ebody) ->
       let px = match ep with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let ep' = impl ctx ep in
       let ebody' = impl (px :: ctx) ebody in
       Cst.Coq_fn (px, ep', ebody')
    | Coq_a_app (ef, ea) ->
       let ef' = impl ctx ef in
       let ea' = impl ctx ea in
       Cst.Coq_app (ef', ea')
    | Coq_a_pi (ep, eret) ->
       let px = match ep with Coq_a_typ _ -> new_tyvar () | _ -> new_var () in
       let ep' = impl ctx ep in
       let eret' = impl (px :: ctx) eret in
       Cst.Coq_pi (px, ep', eret')
    | Coq_a_sub _ -> failwith "Invalid internal language construct"
  in
  fun exp ->
    reset_var_suffix ();
    reset_tyvar_suffix ();
    impl [] exp

let format_exp f exp = format_obj f (exp_to_obj exp)

(************************************************************)
(* Formatting nf *)
(************************************************************)

let format_nf f nf = format_exp f (nf_to_exp nf)

(************************************************************)
(* Formatting main_result *)
(************************************************************)

let format_main_result (f : Format.formatter) : main_result -> unit =
  let open Format in
  function
  | AllGood (cst_typ, cst_exp, typ, exp, nf) ->
     fprintf f "@[<v 2>Parsed:@ @[<hv 0>%a@ : %a@]@]" format_obj cst_exp
       format_obj cst_typ;
     pp_force_newline f ();
     fprintf f "@[<v 2>Elaborated:@ @[<hv 0>%a@ : %a@]@]" format_exp exp
       format_exp typ;
     pp_force_newline f ();
     fprintf f "@[<v 2>Normalized Result:@ @[<hv 0>%a@ : %a@]@]" format_nf nf
       format_exp typ
  | TypeCheckingFailure (typ, exp) ->
     printf "@[<v 2>Type Checking Failure:@ %a@;<1 -2>is not of@ %a@]"
       format_exp exp format_exp typ
  | ElaborationFailure cst_exp ->
     printf "@[<v 2>Elaboration Failure:@ %a@;<1 -2>cannot be elaborated@]"
       format_obj cst_exp
  | ParserFailure (s, t) ->
     printf "@[<v 2>Parser Failure:@ on %a:@ @ @[<hov 0>%a@]@]"
       Lexer.format_token t pp_print_text
       (ParserMessages.message (Parser.Aut.coq_N_of_state s))
  | ParserTimeout fuel -> printf "@[<v 2>Parser Timeout with Fuel %d@]" fuel
