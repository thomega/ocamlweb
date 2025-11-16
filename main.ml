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

(*i*)
open Filename
open Printf
open Output
open Web
open Doclexer
(*i*)


(*s \textbf{Usage.} Printed on error output. *)

let usage () =
  prerr_endline "";
  prerr_endline "Usage: ocamlweb <options and files>";
  prerr_endline "  -o <file>      write output into <file>";
  prerr_endline "  --dvi          output in DVI format (using latex)";
  prerr_endline "  --ps           output in PostScript format (using dvips)";
  prerr_endline "  --pdf          output in PDF format (using pdflatex)";
  prerr_endline "  --html         output in HTML format (using hevea)";
  prerr_endline "  --hevea-option <opt>";
  prerr_endline "                 pass an option to hevea (HTML output)";
  prerr_endline "  -s             (short) no titles for files";
  prerr_endline "  --noweb        use manual LaTeX sectioning, not WEB";
  prerr_endline "  --header       do not skip the headers of Caml file";
  prerr_endline "  --no-preamble  suppress LaTeX header and trailer";
  prerr_endline "  --no-index     do not output the index";
  prerr_endline "  --extern-defs  keep external definitions in the index";
  prerr_endline "  --impl <file>  consider <file> as a .ml file";
  prerr_endline "  --intf <file>  consider <file> as a .mli file";
  prerr_endline "  --tex <file>   consider <file> as a .tex file";
  prerr_endline "  --latex-option <opt>";
  prerr_endline "                 pass an option to the LaTeX package ocamlweb.sty";
  prerr_endline "  --class-options <opt>";
  prerr_endline "                 set the document class options (default is `12pt')";
  prerr_endline "  --encoding <e> set the character encoding (default is 'utf8')";
  prerr_endline "  --old-fullpage use LaTeX package fullpage with no option";
  prerr_endline "  -p <string>    insert something in LaTeX preamble";
  prerr_endline "  --files <file> read file names to process in <file>";
  prerr_endline "  --quiet        quiet mode";
  prerr_endline "  --no-greek     disable use of greek letters for type variables";
  prerr_endline "";
  prerr_endline
    "On-line documentation at http://www.lri.fr/~filliatr/ocamlweb/\n";
  exit 1


(*s \textbf{License informations.} Printed when using option
    \verb!--warranty!. *)

let copying () =
  prerr_endline "
This program is free software; you can redistribute it and/or modify
it under the terms of the GNU Library General Public License version 2, as
published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

See the GNU Library General Public License version 2 for more details
(enclosed in the file LGPL).";
  flush stderr


(*s \textbf{Banner.} Always printed. Notice that it is printed on error
    output, so that when the output of \ocamlweb\ is redirected this header
    is not (unless both standard and error outputs are redirected, of
    course). *)

let banner () =
  eprintf "This is ocamlweb version %s, compiled on %s\n"
    Version.version Version.date;
  eprintf
    "Copyright (c) 1999-2000 Jean-Christophe Filliâtre and Claude Marché\n";
  eprintf
  "This is free software with ABSOLUTELY NO WARRANTY (use option -warranty)\n";
  flush stderr


(*s \textbf{Separation of files.} Files given on the command line are
    separated according to their type, which is determined by their suffix.
    Implementations and interfaces have respective suffixes \verb!.ml!
    and \verb!.mli! and \LaTeX\ files have suffix \verb!.tex!. *)

let check_if_file_exists f =
  if not (Sys.file_exists f) then begin
    eprintf "\nocamlweb: %s: no such file\n" f;
    exit 1
  end

let what_file f =
  check_if_file_exists f;
  if check_suffix f ".ml" then
    File_impl (make_caml_file f)
  else if check_suffix f ".mli" then
    File_intf (make_caml_file f)
  else if check_suffix f ".mll" then
    File_lex (make_caml_file f)
  else if check_suffix f ".mly" then
    File_yacc (make_caml_file f)
  else if check_suffix f ".tex" then
    File_other f
  else begin
    eprintf "\nocamlweb: don't know what to do with %s\n" f;
    exit 1
  end

(*s \textbf{Reading file names from a file.}
    File names may be given
    in a file instead of being given on the command
    line. [(files_from_file f)] returns the list of file names contained
    in the file named [f]. These file names must be separated by spaces,
    tabulations or newlines.
 *)

let files_from_file f =
  let files_from_channel ch =
    let buf = Buffer.create 80 in
    let l = ref [] in
    try
      while true do
	match input_char ch with
	  | ' ' | '\t' | '\n' ->
	      if Buffer.length buf > 0 then l := (Buffer.contents buf) :: !l;
	      Buffer.clear buf
	  | c ->
	      Buffer.add_char buf c
      done; []
    with End_of_file ->
      List.rev !l
  in
  try
    check_if_file_exists f;
    let ch = open_in f in
    let l = files_from_channel ch in
    close_in ch;l
  with Sys_error s -> begin
    eprintf "\nocamlweb: cannot read from file %s (%s)\n" f s;
    exit 1
  end

(*s \textbf{Parsing of the command line.} Output file, if specified, is kept
    in [output_file]. *)

let output_file = ref ""
let dvi = ref false
let ps = ref false
let pdf = ref false
let html = ref false
let hevea_options = ref ([] : string list)

let parse () =
  let files = ref [] in
  let add_file f = files := f :: !files in
  let rec parse_rec = function
    | [] -> ()

    | ("-header" | "--header") :: rem ->
	skip_header := false; parse_rec rem
    | ("-noweb" | "--noweb" | "-no-web" | "--no-web") :: rem ->
	web := false; parse_rec rem
    | ("-web" | "--web") :: rem ->
	web := true; parse_rec rem
    | ("-nopreamble" | "--nopreamble" | "--no-preamble") :: rem ->
	set_no_preamble true; parse_rec rem
    | ("-p" | "--preamble") :: s :: rem ->
	push_in_preamble s; parse_rec rem
    | ("-p" | "--preamble") :: [] ->
	usage ()
    | ("-noindex" | "--noindex" | "--no-index") :: rem ->
	index := false; parse_rec rem
    | ("-o" | "--output") :: f :: rem ->
	output_file := f; parse_rec rem
    | ("-o" | "--output") :: [] ->
	usage ()
    | ("-s" | "--short") :: rem ->
	short := true; parse_rec rem
    | ("-dvi" | "--dvi") :: rem ->
	dvi := true; parse_rec rem
    | ("-ps" | "--ps") :: rem ->
	ps := true; parse_rec rem
    | ("-pdf" | "--pdf") :: rem ->
	pdf := true; parse_rec rem
    | ("-html" | "--html") :: rem ->
	html := true; parse_rec rem
    | ("-hevea-option" | "--hevea-option") :: [] ->
	usage ()
    | ("-hevea-option" | "--hevea-option") :: s :: rem ->
	hevea_options := s :: !hevea_options; parse_rec rem
    | ("-extern-defs" | "--extern-defs") :: rem ->
	extern_defs := true; parse_rec rem
    | ("-q" | "-quiet" | "--quiet") :: rem ->
	quiet := true; parse_rec rem

    | ("--nogreek" | "--no-greek") :: rem ->
	use_greek_letters := false; parse_rec rem

    | ("-h" | "-help" | "-?" | "--help") :: rem ->
	banner (); usage ()
    | ("-v" | "-version" | "--version") :: _ ->
	banner (); exit 0
    | ("-warranty" | "--warranty") :: _ ->
	copying (); exit 0

    | "--class-options" :: s :: rem ->
	class_options := s; parse_rec rem
    | "--class-options" :: [] ->
	usage ()
    | "--latex-option" :: s :: rem ->
	add_latex_option s; parse_rec rem
    | "--latex-option" :: [] ->
	usage ()
    | "--encoding" :: s :: rem ->
	encoding := s; parse_rec rem
    | "--encoding" :: [] ->
	usage ()
    | "--old-fullpage" :: rem ->
	fullpage_headings := false; parse_rec rem

    | ("-impl" | "--impl") :: f :: rem ->
	check_if_file_exists f;
	let n =
	  if Filename.check_suffix f ".mll" || Filename.check_suffix f ".mly"
          then Filename.chop_extension f else f
	in
	let m = File_impl { caml_filename = f; caml_module = module_name n } in
	add_file m; parse_rec rem
    | ("-impl" | "--impl") :: [] ->
	usage ()
    | ("-intf" | "--intf") :: f :: rem ->
	check_if_file_exists f;
	let i = File_intf { caml_filename = f; caml_module = module_name f } in
	add_file i; parse_rec rem
    | ("-intf" | "--intf") :: [] ->
	usage ()
    | ("-tex" | "--tex") :: f :: rem ->
	add_file (File_other f); parse_rec rem
    | ("-tex" | "--tex") :: [] ->
	usage ()
    | ("-files" | "--files") :: f :: rem ->
	List.iter (fun f -> add_file (what_file f)) (files_from_file f);
	parse_rec rem
    | ("-files" | "--files") :: [] ->
	usage ()
    | f :: rem ->
	add_file (what_file f); parse_rec rem
  in
  parse_rec (List.tl (Array.to_list Sys.argv));
  List.rev !files

(*s The following function produces the output. The default output is
  the \LaTeX\ document: in that case, we just call
  [Web.produce_document].  If option \verb!-dvi!, \verb!-ps!,
  \verb!-pdf!, or \verb!-html! is invoked, then we make calls to
  \verb!latex!, \verb!dvips!, \verb!pdflatex!, and/or \verb!hevea!
  accordingly. *)

let locally dir f x =
  let cwd = Sys.getcwd () in
  try
    Sys.chdir dir; let y = f x in Sys.chdir cwd; y
  with e ->
    Sys.chdir cwd; raise e

let clean_temp_files basefile =
  let remove f = try Sys.remove f with _ -> () in
  remove (basefile ^ ".tex");
  remove (basefile ^ ".log");
  remove (basefile ^ ".aux");
  remove (basefile ^ ".dvi");
  remove (basefile ^ ".ps");
  remove (basefile ^ ".haux");
  remove (basefile ^ ".html")

let clean_and_exit basefile res = clean_temp_files basefile; exit res

let cat file =
  let c = open_in file in
  try
    while true do print_char (input_char c) done
  with End_of_file ->
    close_in c

let copy src dst =
  let cin = open_in src
  and cout = open_out dst in
  try
    while true do Stdlib.output_char cout (input_char cin) done
  with End_of_file ->
    close_in cin; close_out cout

let produce_output fl =
  if not (!dvi || !ps || !pdf || !html) then begin
    if !output_file <> "" then set_output_to_file !output_file;
    produce_document fl
  end else begin
    let texfile = temp_file "ocamlweb" ".tex" in
    let basefile = chop_suffix texfile ".tex" in
    set_output_to_file texfile;
    produce_document fl;
    let latex = if !pdf then "pdflatex" else "latex" in
    let command =
      let file = basename texfile in
      let file =
	if !quiet then sprintf "'\\nonstopmode\\input{%s}'" file else file
      in
      sprintf "(%s %s && %s %s) 1>&2 %s" latex file latex file
	(if !quiet then "> /dev/null" else "")
    in
    let res = locally (dirname texfile) Sys.command command in
    if res <> 0 then begin
      eprintf "Couldn't run LaTeX successfully\n";
      clean_and_exit basefile res
    end;
    let dvifile = basefile ^ ".dvi" in
    if !dvi then begin
      if !output_file <> "" then
	(* we cannot use Sys.rename accross file systems *)
	copy dvifile !output_file
      else
	cat dvifile
    end;
    if !ps then begin
      let psfile =
	if !output_file <> "" then !output_file else basefile ^ ".ps"
      in
      let command =
	sprintf "dvips %s -o %s %s" dvifile psfile
	  (if !quiet then "> /dev/null 2>&1" else "")
      in
      let res = Sys.command command in
      if res <> 0 then begin
	eprintf "Couldn't run dvips successfully\n";
	clean_and_exit basefile res
      end;
      if !output_file = "" then cat psfile
    end;
    if !pdf then begin
      let pdffile = basefile ^ ".pdf" in
      if !output_file <> "" then
	(* we cannot use Sys.rename accross file systems *)
	copy pdffile !output_file
      else
	cat pdffile
    end;
    if !html then begin
      let htmlfile =
	if !output_file <> "" then !output_file else basefile ^ ".html"
      in
      let options = String.concat " " (List.rev !hevea_options) in
      let command =
	sprintf "hevea %s ocamlweb.sty %s -o %s %s" options texfile htmlfile
	  (if !quiet then "> /dev/null 2>&1" else "")
      in
      let res = Sys.command command in
      if res <> 0 then begin
	eprintf "Couldn't run hevea successfully\n";
	clean_and_exit basefile res
      end;
      if !output_file = "" then cat htmlfile
    end;
    clean_temp_files basefile
  end

(*s \textbf{Main program.} Print the banner, parse the command line,
    read the files and then call [produce_document] from module [Web]. *)

let main () =
  let files = parse() in
  if List.length files > 0 then begin
    let l = List.map read_one_file files in
    if !web_style then begin
      if not !web && not !quiet then begin
	eprintf
	  "Warning: web sections encountered while in noweb style, ignored.\n";
	flush stderr
      end
    end else
      web := false;
    if not !web then add_latex_option "noweb";
    produce_output l
  end

let _ = Printexc.catch main ()
