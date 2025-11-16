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

{
  open Printf
  open Lexing
  open Output
  open Web
  open Pretty

(*s Global variables and functions used by the lexer. *)

(* [skip_header] tells whether option \verb|--header| has been
   selected by the user. *)

  let skip_header = ref true

(* for displaying error message if any, [current_file] records the
   name of the file currently read, and [comment_or_string_start] records
   the starting position of the comment or the string currently being
   read. *)

  let current_file = ref ""
  let comment_or_string_start = ref 0

(* [brace_depth] records the current depth of imbrication of braces
   \verb|{..}|, to know in lex files whether we are in an action or
   not. [lexyacc_brace_start] records the position of the starting brace
   of the current action, to display an error message if this brace is
   unclosed. *)

  let in_lexyacc_action = ref false
  let doublepercentcounter = ref 0
  let brace_depth = ref 0
  let lexyacc_brace_start = ref 0

(* [web_style] records if web sections were used anywhere in any file. *)

  let web_style = ref false

(* global variables for temporarily recording data, for building
   the [Web.file] structure. *)

  let parbuf = Buffer.create 8192
  let ignoring = ref false

  let push_char c =
    if not !ignoring then Buffer.add_char parbuf c
  let push_first_char lexbuf =
    if not !ignoring then Buffer.add_char parbuf (lexeme_char lexbuf 0)
  let push_string s =
    if not !ignoring then Buffer.add_string parbuf s

  let subparlist = ref ([] : sub_paragraph list)

  let push_caml_subpar () =
    if Buffer.length parbuf > 0 then begin
      subparlist := (CamlCode (Buffer.contents parbuf)) :: !subparlist;
      Buffer.clear parbuf
    end

  let push_lex_subpar () =
    if Buffer.length parbuf > 0 then begin
      subparlist := (LexCode (Buffer.contents parbuf)) :: !subparlist;
      Buffer.clear parbuf
    end

  let push_yacc_subpar () =
    if Buffer.length parbuf > 0 then begin
      subparlist := (YaccCode (Buffer.contents parbuf)) :: !subparlist;
      Buffer.clear parbuf
    end

  let parlist = ref ([] : paragraph list)
  let code_beg = ref 0

  let push_code () =
    assert (List.length !subparlist = 0);
    if Buffer.length parbuf > 0 then begin
      parlist := (Code (!code_beg, Buffer.contents parbuf)) :: !parlist;
      Buffer.clear parbuf
    end

  let push_lexyacccode () =
    assert (Buffer.length parbuf = 0) ;
    if List.length !subparlist > 0 then begin
      parlist := (LexYaccCode (!code_beg, List.rev !subparlist)) :: !parlist;
      subparlist := []
    end

  let big_section = ref false

  let initial_spaces = ref 0

  let push_doc () =
    if Buffer.length parbuf > 0 then begin
      let doc =
	Documentation (!big_section, !initial_spaces, Buffer.contents parbuf)
      in
      parlist := doc :: !parlist;
      big_section := false;
      Buffer.clear parbuf
    end

  let push_latex () =
    if Buffer.length parbuf > 0 then begin
      let doc =
	RawLaTeX (Buffer.contents parbuf)
      in
      parlist := doc :: !parlist;
      big_section := false;
      Buffer.clear parbuf
    end

  let seclist = ref ([] : raw_section list)
  let section_beg = ref 0

  let push_section () =
    if !parlist <> [] then begin
      let s = { sec_contents = List.rev !parlist; sec_beg = !section_beg } in
      seclist := s :: !seclist;
      parlist := []
    end

  let reset_lexer f =
    current_file := f;
    comment_or_string_start := 0;
    section_beg := 0;
    code_beg := 0;
    parlist := [];
    seclist := [];
    in_lexyacc_action := false;
    doublepercentcounter := 0

  let backtrack lexbuf =
    (*i
    eprintf "backtrack to %d\n" (lexbuf.lex_abs_pos + lexbuf.lex_start_pos);
    i*)
    lexbuf.lex_curr_pos <- lexbuf.lex_start_pos

}

(*s Shortcuts for regular expressions. *)

let space = [' ' '\r' '\t']
let space_or_nl = [' ' '\t' '\r' '\n']
let character =
  "'" ( [^ '\\' '\''] | '\\' ['\\' '\'' 'n' 't' 'b' 'r']
      | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] ) "'"
let up_to_end_of_comment =
  [^ '*']* '*' (([^ '*' ')'] [^ '*']* '*') | '*')* ')'

(*s Entry point to skip the headers. Returns when headers are skipped. *)
rule header = parse
  | "(*"
      { comment_or_string_start := lexeme_start lexbuf;
	skip_comment lexbuf;
	skip_spaces_until_nl lexbuf;
	header lexbuf }
  | "\n"
      { () }
  | space+
      { header lexbuf }
  | _
      { backtrack lexbuf }
  | eof
      { () }

(* To skip a comment (used by [header]). *)
and skip_comment = parse
  | "(*"
      { skip_comment lexbuf; skip_comment lexbuf }
  | "*)"
      { () }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocaml comment\n";
	exit 1 }
  | _
      { skip_comment lexbuf }

(*s Same as [header] but for \textsf{OCamlYacc} *)
and yacc_header = parse
  | "/*"
      { comment_or_string_start := lexeme_start lexbuf;
	skip_yacc_comment lexbuf;
	skip_spaces_until_nl lexbuf;
	yacc_header lexbuf }
  | "\n"
      { () }
  | space+
      { yacc_header lexbuf }
  | _
      { backtrack lexbuf }
  | eof
      { () }

and skip_yacc_comment = parse
  | "/*"
      { skip_yacc_comment lexbuf; skip_yacc_comment lexbuf }
  | "*/"
      { () }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocamlyacc comment\n";
	exit 1 }
  | _
      { skip_yacc_comment lexbuf }


(*s Recognizes a complete caml module body or interface, after header
has been skipped. After calling that entry, the whole text read is in
[seclist]. *)

and caml_implementation = parse
  | _
      { backtrack lexbuf;
	paragraph lexbuf;
	caml_implementation lexbuf }
  | eof
      { push_section () }

(* recognizes a paragraph of caml code or documentation. After calling
  that entry, the paragraph has been added to [parlist]. *)

and paragraph = parse
  | space* '\n'
      { paragraph lexbuf }
  | space* ";;"
      { paragraph lexbuf }
  | space* "(*" '*'* "*)" space* '\n'
      { paragraph lexbuf }
  | space* "(*"
      { comment_or_string_start := lexeme_start lexbuf;
	let s = lexeme lexbuf in
	initial_spaces := count_spaces (String.sub s 0 (String.length s - 2));
	start_of_documentation lexbuf;
	push_doc () }
  | space* ("(*c" | _)
      { code_beg := lexeme_start lexbuf;
	backtrack lexbuf;
	caml_subparagraph lexbuf;
	push_code() }
  | eof
      { () }

(* recognizes a whole lex description file, after header has been
skipped. After calling that entry, the whole text read is in
[seclist]. *)

and lex_description = parse
  | _
      { backtrack lexbuf;
	lex_paragraph lexbuf ;
	lex_description lexbuf }
  | eof
      { push_section () }

and yacc_description = parse
  | _
      { backtrack lexbuf ;
	yacc_paragraph lexbuf;
	yacc_description lexbuf }
  | eof
      { push_section () }

(* Recognizes a paragraph of a lex description file. After calling
  that entry, the paragraph has been added to [parlist]. *)

and lex_paragraph = parse
  | space* '\n'
      { lex_paragraph lexbuf }
  | space* "(*" '*'* "*)" space* '\n'
      { lex_paragraph lexbuf }
  | space* ("(*c" | _)
      { code_beg := lexeme_start lexbuf;
	backtrack lexbuf;
	lex_subparagraphs lexbuf ;
	push_lexyacccode() }
  | space* "(*"
      { comment_or_string_start := lexeme_start lexbuf;
	start_of_documentation lexbuf;
	push_doc () }
  | eof
      { () }

and yacc_paragraph = parse
  | space* '\n'
      { yacc_paragraph lexbuf }
  | space* "/*" '*'* "*/" space* '\n'
      { if not !in_lexyacc_action
	then yacc_paragraph lexbuf
	else begin
	  code_beg := lexeme_start lexbuf;
	  backtrack lexbuf;
	  yacc_subparagraphs lexbuf ;
	  push_lexyacccode()
	end }
  | space* "/*"
      { if not !in_lexyacc_action
	then begin
	  comment_or_string_start := lexeme_start lexbuf;
	  start_of_yacc_documentation lexbuf;
	  push_doc ()
	end
	else begin
	  code_beg := lexeme_start lexbuf;
	  backtrack lexbuf;
	  yacc_subparagraphs lexbuf ;
	  push_lexyacccode()
	end }
  | space* "(*" '*'* "*)" space* '\n'
      { if !in_lexyacc_action
	then yacc_paragraph lexbuf
	else begin
	  code_beg := lexeme_start lexbuf;
	  backtrack lexbuf;
	  yacc_subparagraphs lexbuf ;
	  push_lexyacccode()
	end }
  | space* "(*"
      { if !in_lexyacc_action
	then begin
	  comment_or_string_start := lexeme_start lexbuf;
	  start_of_documentation lexbuf;
	  push_doc ()
	end
	else begin
	  code_beg := lexeme_start lexbuf;
	  backtrack lexbuf;
	  yacc_subparagraphs lexbuf ;
	  push_lexyacccode()
	end }
  | space* ("/*c" | "(*c" | _)
      { code_beg := lexeme_start lexbuf;
	backtrack lexbuf;
	yacc_subparagraphs lexbuf ;
	push_lexyacccode() }
  | eof
      { () }

(*s At the beginning of the documentation part, just after the
  \verb|"(*"|. If the first character is ['s'], then a new section is
  started. After calling that entry, the [parbuf] buffer contains the
  doc read. *)
(*i "*)" i*)

and start_of_documentation = parse
  | space_or_nl+
      { in_documentation lexbuf }
  | ('s' | 'S') space_or_nl*
      { web_style := true; push_section ();
	section_beg := lexeme_start lexbuf;
	big_section := (lexeme_char lexbuf 0 == 'S');
	in_documentation lexbuf }
  | 'p' up_to_end_of_comment
      { let s = lexeme lexbuf in
	push_in_preamble (String.sub s 1 (String.length s - 3)) }
  | 'i'
      { ignore lexbuf }
  | 'l'
      { in_documentation lexbuf; push_latex () }
  | _
      { backtrack lexbuf;
	in_documentation lexbuf }
  | eof
      { in_documentation lexbuf }

and start_of_yacc_documentation = parse
  | space_or_nl+
      { in_yacc_documentation lexbuf }
  | ('s' | 'S') space_or_nl*
      { web_style := true; push_section ();
	section_beg := lexeme_start lexbuf;
	big_section := (lexeme_char lexbuf 0 == 'S');
	in_yacc_documentation lexbuf }
  | 'p' up_to_end_of_comment
      { let s = lexeme lexbuf in
	push_in_preamble (String.sub s 1 (String.length s - 3)) }
  | 'i'
      { yacc_ignore lexbuf }
  | 'l'
      { in_yacc_documentation lexbuf; push_latex () }
  | _
      { backtrack lexbuf;
	in_yacc_documentation lexbuf }
  | eof
      { in_yacc_documentation lexbuf }

(*s Inside the documentation part, anywhere after the "(*". After
  calling that entry, the [parbuf] buffer contains the doc read. *)
(*i "*)" i*)

and in_documentation = parse
  | "(*"
      { push_string "(*";
	in_documentation lexbuf;
	push_string "*)";
	in_documentation lexbuf }
  | "*)"
      { () }
  | '\n' " * "
      { push_char '\n'; in_documentation lexbuf }
  | '"'
      { push_char '"'; in_string lexbuf; in_documentation lexbuf }
  | character
      { push_string (lexeme lexbuf); in_documentation lexbuf }
  | _
      { push_first_char lexbuf; in_documentation lexbuf }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocaml comment\n";
	exit 1  }

(* yacc comments are NOT nested *)

and in_yacc_documentation = parse
  | "*/"
      { () }
  | '\n' " * "
      { push_char '\n'; in_yacc_documentation lexbuf }
  | '"'
      { push_char '"'; in_string lexbuf; in_yacc_documentation lexbuf }
  | character
      { push_string (lexeme lexbuf); in_yacc_documentation lexbuf }
  | _
      { push_first_char lexbuf; in_yacc_documentation lexbuf }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocamlyacc comment\n";
	exit 1  }

(*s Recognizes a subparagraph of caml code. After calling that entry,
  the [parbuf] buffer contains the code read. *)

and caml_subparagraph = parse
  | space* '\n' space* '\n'
      { backtrack lexbuf }
  | ";;"
      { backtrack lexbuf }
  | eof
      { () }
  | "(*" | "(*c"
      { comment_or_string_start := lexeme_start lexbuf;
	push_string "(*";
	comment lexbuf;
	caml_subparagraph lexbuf }
  | "(*i"
         { comment_or_string_start := lexeme_start lexbuf;
	   ignore lexbuf; caml_subparagraph lexbuf }
  | '"'  { comment_or_string_start := lexeme_start lexbuf;
           push_char '"'; in_string lexbuf; caml_subparagraph lexbuf }
  | '{'  { incr brace_depth;
           push_char '{';
           caml_subparagraph lexbuf }
  | '}'
      { if !brace_depth = 0 then backtrack lexbuf
        else
          begin
            decr brace_depth;
            push_char '}';
            caml_subparagraph lexbuf
          end }
  | "%}"
      { if !brace_depth = 0 then backtrack lexbuf
        else
          begin
            decr brace_depth;
            push_string "%}";
            caml_subparagraph lexbuf
          end }
  | character
         { push_string (lexeme lexbuf); caml_subparagraph lexbuf }
  | _    { push_first_char lexbuf; caml_subparagraph lexbuf }

(*s Recognizes a sequence of subparagraphs of lex description,
  including CAML actions. After calling that entry, the subparagraphs
  read are in [subparlist]. *)

and lex_subparagraphs = parse
  | space* '\n' space* '\n'
      { backtrack lexbuf }
  | ";;"
      { () }
  | eof
      { if !in_lexyacc_action
	then
	  begin
	    eprintf "File \"%s\", character %d\n"
	      !current_file !lexyacc_brace_start;
	    eprintf "Unclosed brace\n" ;
	    exit 1
	  end }
  | '}'
      { if !in_lexyacc_action
	then
	  begin
	    push_char '}';
	    in_lexyacc_action := false;
	    lex_subparagraph lexbuf;
	    push_lex_subpar();
	    lex_subparagraphs lexbuf
	  end
	else
	  begin
	    eprintf "File \"%s\", character %d\n"
	      !current_file (lexeme_start lexbuf);
	    eprintf "Unexpected closing brace ";
	    exit 1
	  end }
  | _
      { backtrack lexbuf;
	if !in_lexyacc_action
	then
	  begin
	    caml_subparagraph lexbuf;
	    push_caml_subpar()
	  end
	else
	  begin
	    lex_subparagraph lexbuf;
	    push_lex_subpar()
	  end;
        lex_subparagraphs lexbuf }

and yacc_subparagraphs = parse
  | space* '\n' space* '\n'
      { backtrack lexbuf }
  | "%%"
      { if !in_lexyacc_action then begin
	  push_string "%%";
	  caml_subparagraph lexbuf;
	  push_caml_subpar();
          yacc_subparagraphs lexbuf
	end
	else begin
	  push_yacc_subpar();
	  push_string "%%";
	  push_yacc_subpar();
	  incr doublepercentcounter;
	  if !doublepercentcounter >= 2 then in_lexyacc_action := true
	end }
  | ";;"
      { if !in_lexyacc_action then ()
	else begin
	  push_string ";;";
	  yacc_subparagraph lexbuf;
	  push_yacc_subpar();
          yacc_subparagraphs lexbuf
	end }
  | eof
      { if !in_lexyacc_action && !doublepercentcounter <= 1
	then
	  begin
	    eprintf "File \"%s\", character %d\n"
	      !current_file !lexyacc_brace_start;
	    eprintf "Unclosed brace\n" ;
	    exit 1
	  end }
  | '}'
      { if !in_lexyacc_action
	then
	  begin
	    push_char '}';
	    in_lexyacc_action := false;
	    yacc_subparagraph lexbuf;
	    push_yacc_subpar();
	    yacc_subparagraphs lexbuf
	  end
	else
	  begin
	    eprintf "File \"%s\", character %d\n"
	      !current_file (lexeme_start lexbuf);
	    eprintf "Unexpected closing brace ";
	    exit 1
	  end }
  | "%}"
      { if !in_lexyacc_action
	then
	  begin
	    push_string "%}";
	    in_lexyacc_action := false;
	    yacc_subparagraph lexbuf;
	    push_yacc_subpar();
	    yacc_subparagraphs lexbuf
	  end
	else
	  begin
	    eprintf "File \"%s\", character %d\n"
	      !current_file (lexeme_start lexbuf);
	    eprintf "Unexpected closing brace ";
	    exit 1
	  end }
  | _
      { backtrack lexbuf;
	if !in_lexyacc_action
	then
	  begin
	    caml_subparagraph lexbuf;
	    push_caml_subpar()
	  end
	else
	  begin
	    yacc_subparagraph lexbuf;
	    push_yacc_subpar()
	  end;
        yacc_subparagraphs lexbuf }


(*s Recognizes a subparagraph of lex description. After
  calling that entry, the subparagraph read is in [parbuf]. *)

and lex_subparagraph = parse
  | space* '\n' space* '\n'
         { backtrack lexbuf }
  | ";;" { backtrack lexbuf }
  | eof  { () }
  | "(*" | "(*c"
         { comment_or_string_start := lexeme_start lexbuf;
	   push_string "(*";
	   comment lexbuf;
	   lex_subparagraph lexbuf }
  | space* "(*i"
         { comment_or_string_start := lexeme_start lexbuf;
	   ignore lexbuf; lex_subparagraph lexbuf }
  | '"'  { comment_or_string_start := lexeme_start lexbuf;
	   push_char '"'; in_string lexbuf; lex_subparagraph lexbuf }
  | '{'
      { lexyacc_brace_start := lexeme_start lexbuf;
	push_char '{';
	in_lexyacc_action := true }
  | character
      { push_string (lexeme lexbuf); lex_subparagraph lexbuf }
  | _
      { push_first_char lexbuf; lex_subparagraph lexbuf }


and yacc_subparagraph = parse
  | space* '\n' space* '\n'
         { backtrack lexbuf }
  | "%%" { backtrack lexbuf }
  | ";;" { backtrack lexbuf }
  | eof  { () }
  | "/*" | "/*c"
         { comment_or_string_start := lexeme_start lexbuf;
	   push_string "/*";
	   yacc_comment lexbuf;
	   yacc_subparagraph lexbuf }
  | space* "/*i"
         { comment_or_string_start := lexeme_start lexbuf;
	   yacc_ignore lexbuf; yacc_subparagraph lexbuf }
  | '"'  { comment_or_string_start := lexeme_start lexbuf;
	   push_char '"'; in_string lexbuf; yacc_subparagraph lexbuf }
  | "%{"
      { lexyacc_brace_start := lexeme_start lexbuf;
	push_string "%{";
	in_lexyacc_action := true }
  | '{'
      { lexyacc_brace_start := lexeme_start lexbuf;
	push_char '{';
	in_lexyacc_action := true }
  | '<'
      { lexyacc_brace_start := lexeme_start lexbuf;
	push_char '<';
	push_yacc_subpar ();
	yacc_type lexbuf;
	yacc_subparagraph lexbuf }
  | character
      { push_string (lexeme lexbuf); yacc_subparagraph lexbuf }
  | _
      { push_first_char lexbuf; yacc_subparagraph lexbuf }

and yacc_type = parse
  | "->"
      { push_string "->"; yacc_type lexbuf }
  | '>'
      { push_caml_subpar(); push_char '>' }
  | _
      { push_first_char lexbuf; yacc_type lexbuf }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !lexyacc_brace_start;
	eprintf "Unclosed '<'";
	exit 1 }

(*s To skip spaces until a newline. *)
and skip_spaces_until_nl = parse
  | space* '\n'? { () }
  | eof  { () }
  | _    { backtrack lexbuf }


(*s To read a comment inside a piece of code. *)
and comment = parse
  | "(*" | "(*c"
      { push_string "(*"; comment lexbuf; comment lexbuf }
  | "*)"
      { push_string "*)"  }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocaml comment\n";
	exit 1 }
  | _
      { push_first_char lexbuf; comment lexbuf }

and yacc_comment = parse
  | "*/"
      { push_string "*/"  }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocamlyacc comment\n";
	exit 1 }
  | _
      { push_first_char lexbuf; yacc_comment lexbuf }

(*s Ignored parts, between "(*i" and "i*)". Note that such comments
    are not nested. *)
and ignore = parse
  | "i*)"
      { skip_spaces_until_nl lexbuf }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocamlweb comment\n";
	exit 1 }
  | _
      { ignore lexbuf }

and yacc_ignore = parse
  | "i*/"
      { skip_spaces_until_nl lexbuf }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocamlweb comment\n";
	exit 1 }
  | _
      { yacc_ignore lexbuf }

(*s Strings in code. *)
and in_string = parse
  | '"'
      { push_char '"' }
  | '\\' ['\\' '"' 'n' 't' 'b' 'r']
      { push_string (lexeme lexbuf); in_string lexbuf }
  | eof
      { eprintf "File \"%s\", character %d\n"
	  !current_file !comment_or_string_start;
	eprintf "Unterminated ocaml string\n";
	exit 1 }
  | _
      { push_first_char lexbuf; in_string lexbuf }


{

(*s \textbf{Caml files.} *)

type caml_file = { caml_filename : string; caml_module : string }

let module_name f = String.capitalize_ascii (Filename.basename f)

let make_caml_file f =
  { caml_filename = f;
    caml_module = module_name (Filename.chop_extension f) }

type file_type =
  | File_impl  of caml_file
  | File_intf  of caml_file
  | File_lex   of caml_file
  | File_yacc  of caml_file
  | File_other of string

(*s \textbf{Reading Caml files.} *)

let raw_read_file header entry f =
  reset_lexer f;
  let c = open_in f in
  let buf = Lexing.from_channel c in
  if !skip_header then header buf;
  entry buf;
  close_in c;
  List.rev !seclist

let read header entry m =
  { content_file = m.caml_filename;
    content_name = m.caml_module;
    content_contents = raw_read_file header entry m.caml_filename; }

let read_one_file = function
  | File_impl m -> Implem (read header caml_implementation m)
  | File_intf m -> Interf (read header caml_implementation m)
  | File_lex  m -> Lex (read header lex_description m)
  | File_yacc m -> Yacc (read yacc_header yacc_description m)
  | File_other f -> Other f

}

