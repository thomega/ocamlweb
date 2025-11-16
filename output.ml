(*
 * ocamlweb - A WEB-like tool for ocaml
 * Copyright (C) 1999-2001 Jean-Christophe FILLIÂTRE and Claude MARCHÉ
 *
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 *
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file LGPL).
 *)

(*i $Id$ i*)

(*i*)
open Printf
(*i*)

(*s \textbf{Low level output.}
   [out_channel] is a reference on the current output channel.
   It is initialized to the standard output and can be
   redirect to a file by the function [set_output_to_file].
   The function [close_output] closes the output channel if it is a file.
   [output_char], [output_string] and [output_file] are self-explainable.
 *)

let out_channel = ref stdout
let output_is_file = ref false

let set_output_to_file f =
  out_channel := open_out f;
  output_is_file := true

let close_output () =
  if !output_is_file then close_out !out_channel

let quiet = ref false

let short = ref false

let output_char c = Stdlib.output_char !out_channel c

let output_string s = Stdlib.output_string !out_channel s

let output_file f =
  let ch = open_in f in
  try
    while true do
      Stdlib.output_char !out_channel (input_char ch)
    done
  with End_of_file -> close_in ch


(*s \textbf{High level output.}
    In this section and the following, we introduce functions which are
    \LaTeX\ dependent. *)

(*s [output_verbatim] outputs a string in verbatim mode.
    A valid delimiter is given by the function [char_out_of_string].
    It assumes that one of the four characters of [fresh_chars] is not used
    (which is the case in practice, since [output_verbatim] is only used
    to print quote-delimited characters). *)

let fresh_chars = [ '!'; '|'; '"'; '+' ]

let char_out_of_string s =
  let rec search = function
    | [] -> assert false
    | c :: r -> if String.contains s c then search r else c
  in
  search fresh_chars

let output_verbatim s =
  let c = char_out_of_string s in
  output_string (sprintf "\\verb%c%s%c" c s c)

let no_preamble = ref false

let set_no_preamble b = no_preamble := b

let (preamble : string Queue.t) = Queue.create ()

let push_in_preamble s = Queue.add s preamble

let class_options = ref "12pt"

let fullpage_headings = ref true

let encoding = ref "utf8"

let latex_header opt =
  if not !no_preamble then begin
    output_string (sprintf "\\documentclass[%s]{article}\n" !class_options);
    output_string (sprintf "\\usepackage[%s]{inputenc}\n" !encoding);
    (*i output_string "\\usepackage[T1]{fontenc}\n"; i*)
    if !fullpage_headings then
      output_string "\\usepackage[headings]{fullpage}\n"
    else
      output_string "\\usepackage{fullpage}\n";
    output_string "\\usepackage";
    if opt <> "" then output_string (sprintf "[%s]" opt);
    output_string "{ocamlweb}\n";
    output_string "\\pagestyle{headings}\n";
    Queue.iter (fun s -> output_string s; output_string "\n") preamble;
    output_string "\\begin{document}\n"
  end;
  output_string
    "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";
  output_string
    "%% This file has been automatically generated with the command\n";
  output_string "%% ";
  Array.iter (fun s -> output_string s; output_string " ") Sys.argv;
  output_string "\n";
  output_string
    "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"

let latex_trailer () =
  if not !no_preamble then begin
    output_string "\\end{document}\n"
  end


(*s \textbf{Math mode.}
    We keep a boolean, [math_mode], to know if we are currently
    already in \TeX\ math mode. The functions [enter_math] and [leave_math]
    inserts \verb!$! if necessary, and switch that boolean.
 *)

let math_mode = ref false

let enter_math () =
  if not !math_mode then begin
    output_string "$";
    math_mode := true
  end

let leave_math () =
  if !math_mode then begin
    output_string "$";
    math_mode := false
  end


(*s \textbf{Indentation.}
    An indentation at the beginning of a line of $n$ spaces
    is produced by [(indentation n)] (used for code only). *)

let indentation n =
  let space = 0.5 *. (float n) in
  output_string (sprintf "\\ocwindent{%2.2fem}\n" space)


(*s \textbf{End of lines.}
    [(end_line ())] ends a line. (used for code only). *)

let end_line () =
  leave_math ();
  output_string "\\ocweol\n"

let end_line_string () =
  output_string "\\endgraf\n"


(*s \textbf{Keywords.}
    Caml keywords and base type are stored in two hash tables, and the two
    functions [is_caml_keyword] and [is_base_type] make the corresponding
    tests.
    The function [output_keyword] prints a keyword, with different macros
    for base types and keywords.
  *)

let build_table l =
  let h = Hashtbl.create 101 in
  List.iter (fun key -> Hashtbl.add h  key ()) l;
  Hashtbl.mem h

let is_caml_keyword =
  build_table
    [ "and"; "as";  "assert"; "begin"; "class";
      "constraint"; "do"; "done";  "downto"; "else"; "end"; "exception";
      "external";  "false"; "for";  "fun"; "function";  "functor"; "if";
      "in"; "include"; "inherit"; "initializer"; "lazy"; "let"; "match";
      "method";  "module";  "mutable";  "new"; "object";  "of";  "open";
      "or"; "parser";  "private"; "rec"; "sig";  "struct"; "then"; "to";
      "true"; "try"; "type"; "val"; "virtual"; "when"; "while"; "with";
      "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"
    ]

let is_base_type =
  build_table
    [ "string"; "int"; "array"; "unit"; "bool"; "char"; "list"; "option";
      "float"; "ref" ]

let is_lex_keyword =
  build_table
    [ "rule"; "let"; "and"; "parse"; "eof"; "as" ]

let is_yacc_keyword =
  build_table
    [ "%token"; "%left"; "%right"; "%type"; "%start"; "%nonassoc"; "%prec";
      "error" ]


let is_keyword s = is_base_type s || is_caml_keyword s


let output_keyword s =
  if is_base_type s then
    output_string "\\ocwbt{"
  else
    output_string "\\ocwkw{";
  output_string s;
  output_string "}"

let output_lex_keyword s =
  output_string "\\ocwlexkw{";
  output_string s;
  output_string "}"

let output_yacc_keyword s =
  output_string "\\ocwyacckw{";
  if String.get s 0 = '%' then output_string "\\";
  output_string s;
  output_string "}"

(*s \textbf{Identifiers.}
    The function [output_raw_ident] prints an identifier,
    escaping the \TeX\ reserved characters with [output_escaped_char].
    The function [output_ident] prints an identifier, calling
    [output_keyword] if necessary.
 *)

let output_escaped_char c =
  if c = '^' || c = '~' then leave_math();
  match c with
    | '\\' ->
	output_string "\\symbol{92}"
    | '$' | '#' | '%' | '&' | '{' | '}' | '_' ->
	output_char '\\'; output_char c
    | '^' | '~' ->
	output_char '\\'; output_char c; output_string "{}"
    | '<' | '>' ->
        output_string "\\ensuremath{"; output_char c; output_string "}"
    | _ ->
	output_char c

let output_latex_id s =
  for i = 0 to String.length s - 1 do
    output_escaped_char s.[i]
  done

type char_type = Upper | Lower | Symbol

let what_char = function
  | 'A'..'Z' | '\192'..'\214' | '\216'..'\222' -> Upper
  | 'a'..'z' |'\223'..'\246' | '\248'..'\255' | '_' -> Lower
  | _ -> Symbol

let what_is_first_char s =
  if String.length s > 0 then what_char s.[0] else Lower

let output_raw_ident_in_index s =
  begin match what_is_first_char s with
    | Upper -> output_string "\\ocwupperid{"
    | Lower -> output_string "\\ocwlowerid{"
    | Symbol -> output_string "\\ocwsymbolid{"
  end;
  output_latex_id s;
  output_string "}"

let output_raw_ident s =
  begin match what_is_first_char s with
    | Upper -> output_string "\\ocwupperid{"
    | Lower -> output_string "\\ocwlowerid{"
    | Symbol -> output_string "\\ocwsymbolid{"
  end;
  try
    let qualification = Filename.chop_extension s in
    (* We extract the qualified name. *)
    let qualified_name =
      String.sub s (String.length qualification + 1)
	(String.length s - String.length qualification - 1)
    in
    (* We check now whether the qualified term is a lower id or not. *)
    match qualified_name.[0] with
      | 'A'..'Z' ->
      (* The qualified term is a module or a constructor: nothing to change. *)
          output_latex_id (s);
          output_string "}"
      | _ ->
      (* The qualified term is a value or a type:
	 \verb!\\ocwlowerid! used instead. *)
          output_latex_id (qualification ^ ".");
          output_string "}";
          output_string "\\ocwlowerid{";
          output_latex_id qualified_name;
          output_string "}"
  with Invalid_argument _ ->
    (* The string [s] is a module name or a constructor: nothing to do. *)
    output_latex_id s;
    output_string "}"

let output_ident s =
  if is_keyword s then begin
    leave_math (); output_keyword s
  end else begin
    enter_math (); output_raw_ident s
  end

let output_lex_ident s =
  if is_lex_keyword s then begin
    leave_math (); output_lex_keyword s
  end else begin
    enter_math ();
    output_string "\\ocwlexident{";
    output_latex_id s;
    output_string "}";
  end

let output_yacc_ident s =
  if is_yacc_keyword s then begin
    leave_math (); output_yacc_keyword s
  end else begin
    enter_math ();
    output_string "\\ocwyaccident{";
    output_latex_id s;
    output_string "}";
  end

(*s \textbf{Symbols.}
    Some mathematical symbols are printed in a nice way, in order
    to get a more readable code.
    The type variables from \verb!'a! to \verb!'d! are printed as Greek
    letters for the same reason.
 *)

let output_symbol = function
  | "*"  -> enter_math (); output_string "\\times{}"
  | "**" -> enter_math (); output_string "*\\!*"
  | "->" -> enter_math (); output_string "\\rightarrow{}"
  | "<-" -> enter_math (); output_string "\\leftarrow{}"
  | "<=" -> enter_math (); output_string "\\le{}"
  | ">=" -> enter_math (); output_string "\\ge{}"
  | "<>" -> enter_math (); output_string "\\not="
  | "==" -> enter_math (); output_string "\\equiv"
  | "!=" -> enter_math (); output_string "\\not\\equiv"
  | "~-" -> enter_math (); output_string "-"
  | "[<" -> enter_math (); output_string "[\\langle{}"
  | ">]" -> enter_math (); output_string "\\rangle{}]"
  | "<" | ">" | "(" | ")" | "[" | "]" | "[|" | "|]" as s ->
            enter_math (); output_string s
  | "&" | "&&" ->
            enter_math (); output_string "\\land{}"
  | "or" | "||" ->
            enter_math (); output_string "\\lor{}"
  | "not" -> enter_math (); output_string "\\lnot{}"
  | "[]" -> enter_math (); output_string "[\\,]"
  | "|" -> enter_math (); output_string "\\mid{}"
  | s    -> output_latex_id s

let use_greek_letters = ref true

let output_tv id =
  output_string "\\ocwtv{"; output_latex_id id; output_char '}'

let output_greek l =
  enter_math (); output_char '\\'; output_string l; output_string "{}"

let output_type_variable id =
  if not !use_greek_letters then
    output_tv id
  else
    match id with
      | "a" -> output_greek "alpha"
      | "b" -> output_greek "beta"
      | "c" -> output_greek "gamma"
      | "d" -> output_greek "delta"
      | "e" -> output_greek "varepsilon"
      | "i" -> output_greek "iota"
      | "k" -> output_greek "kappa"
      | "l" -> output_greek "lambda"
      | "m" -> output_greek "mu"
      | "n" -> output_greek "nu"
      | "r" -> output_greek "rho"
      | "s" -> output_greek "sigma"
      | "t" -> output_greek "tau"
      | _   -> output_tv id

let output_ascii_char n =
  output_string (sprintf "\\symbol{%d}" n)

(*s \textbf{Constants.} *)

let output_integer s =
  let n = String.length s in
  let base b =
    let v = String.sub s 2 (n - 2) in
    output_string (sprintf "\\ocw%sconst{%s}" b v)
  in
  if n > 1 then
    match s.[1] with
      | 'x' | 'X' -> base "hex"
      | 'o' | 'O' -> base "oct"
      | 'b' | 'B' -> base "bin"
      | _ -> output_string s
  else
    output_string s

let output_float s =
  try
    let i = try String.index s 'e' with Not_found -> String.index s 'E' in
    let m = String.sub s 0 i in
    let e = String.sub s (succ i) (String.length s - i - 1) in
    if m = "1" then
      output_string (sprintf "\\ocwfloatconstexp{%s}" e)
    else
      output_string (sprintf "\\ocwfloatconst{%s}{%s}" m e)
  with Not_found ->
    output_string s


(*s \textbf{Comments.} *)

let output_bc () = leave_math (); output_string "\\ocwbc{}"

let output_ec () = leave_math (); output_string "\\ocwec{}"

let output_hfill () = leave_math (); output_string "\\hfill "

let output_byc () = leave_math (); output_string "\\ocwbyc{}"

let output_eyc () = leave_math (); output_string "\\ocweyc{}"

(*s \textbf{Strings.} *)

let output_bs () = leave_math (); output_string "\\ocwstring{\""

let output_es () = output_string "\"}"

let output_vspace () = output_string "\\ocwvspace{}"


(*s Reset of the output machine. *)

let reset_output () =
  math_mode := false


(*s \textbf{Sectioning commands.} *)

let begin_section () =
  output_string "\\allowbreak\\ocwsection\n"

let output_typeout_command filename =
  output_string "\\typeout{OcamlWeb file ";
  output_string filename;
  output_string "}\n"

let output_module module_name =
  if not !short then begin
    output_typeout_command (module_name^".ml");
    output_string "\\ocwmodule{";
    output_latex_id module_name;
    output_string "}\n"
  end

let output_interface module_name =
  if not !short then begin
    output_typeout_command (module_name^".mli");
    output_string "\\ocwinterface{";
    output_latex_id module_name;
    output_string "}\n"
  end

let output_lexmodule module_name =
  if not !short then begin
    output_typeout_command (module_name^".mll");
    output_string "\\ocwlexmodule{";
    output_latex_id module_name;
    output_string "}\n"
  end

let output_yaccmodule module_name =
  if not !short then begin
    output_typeout_command (module_name^".mly");
    output_string "\\ocwyaccmodule{";
    output_latex_id module_name;
    output_string "}\n"
  end

let in_code = ref false

let begin_code () =
  if not !in_code then output_string "\\ocwbegincode{}";
  in_code := true
let end_code () =
  if !in_code then output_string "\\ocwendcode{}";
  in_code := false

let begin_dcode () =
  output_string "\\ocwbegindcode{}"
let end_dcode () =
  output_string "\\ocwenddcode{}"

let last_is_code = ref false

let begin_code_paragraph () =
  if not !last_is_code then output_string "\\medskip\n";
  last_is_code := true

let end_code_paragraph is_last_paragraph =
  if is_last_paragraph then end_line() else output_string "\\medskip\n\n"

let begin_doc_paragraph is_first_paragraph n =
  if not is_first_paragraph then indentation n;
  last_is_code := false

let end_doc_paragraph () =
  output_string "\n"


(*s \textbf{Index.}
    It is opened and closed with the two macros \verb!ocwbeginindex! and
    \verb!ocwendindex!.
    The auxiliary function [print_list] is a generic function to print a
    list with a given printing function and a given separator.
  *)

let begin_index () =
  output_string "\n\n\\ocwbeginindex{}\n"

let end_index () =
  output_string "\n\n\\ocwendindex{}\n"

let print_list print sep l =
  let rec print_rec = function
    | [] -> ()
    | [x] -> print x
    | x::r -> print x; sep(); print_rec r
  in
  print_rec l


(*s \textbf{Index in WEB style.}
    The function [output_index_entry] prints one entry line, given the
    name of the entry, and two lists of pre-formatted sections labels,
    like 1--4,7,10--17, of type [string elem list].
    The first list if printed in bold face (places where the identifier is
    defined) and the second one in roman (places where it is used).
 *)

type 'a elem = Single of 'a | Interval of 'a * 'a

let output_ref r = output_string (sprintf "\\ref{%s}" r)

let output_elem = function
  | Single r ->
      output_ref r
  | Interval (r1,r2) ->
      output_ref r1;
      output_string "--";
      output_ref r2

let output_bf_elem n =
  output_string "\\textbf{"; output_elem n; output_string "}"

let output_index_entry s t def use =
  let sep () = output_string ", " in
  output_string "\\ocwwebindexentry{";
  enter_math ();
  output_raw_ident_in_index s;
  leave_math ();
  if t <> "" then output_string (" " ^ t);
  output_string "}{";
  print_list output_bf_elem sep def;
  output_string "}{";
  if def <> [] && use <> [] then output_string ", ";
  print_list output_elem sep use;
  output_string "}\n"


(*s \textbf{Index in \LaTeX\ style.}
    When we are not in WEB style, the index in left to \LaTeX, and all
    the work is done by the macro \verb!\ocwrefindexentry!, which takes
    three arguments: the name of the entry and the two lists of labels where
    it is defined and used, respectively.
 *)

let output_raw_index_entry s t def use =
  let sep () = output_string ","
  and sep' () = output_string ", " in
  output_string "\\ocwrefindexentry{";
  enter_math ();
  output_raw_ident_in_index s;
  leave_math ();
  if t <> "" then output_string (" " ^ t);
  output_string "}{";
  print_list output_string sep def;
  output_string "}{";
  print_list output_string sep use;
  output_string "}{";
  print_list output_ref sep' def;
  output_string "}{";
  print_list output_ref sep' use;
  output_string "}\n"

let output_label l =
  output_string "\\label{"; output_string l; output_string "}%\n"
