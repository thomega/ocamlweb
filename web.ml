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

open Filename
open Cross
open Output
open Pretty

(*i*)


type sub_paragraph =
  | CamlCode of string
  | LexCode  of string
  | YaccCode of string

type paragraph =
  | Documentation of bool * int * string
  | RawLaTeX of string
  | Code of int * string
  | LexYaccCode of int * (sub_paragraph list)

type raw_section =  {
  sec_contents : paragraph list;
  sec_beg : int }

type content = {
  content_file : string;
  content_name : string;
  content_contents : raw_section list }

type file =
  | Implem of content
  | Interf of content
  | Lex    of content
  | Yacc   of content
  | Other  of string



(*i To print a "Web.file" (for testing) *)

let print_string s = Format.printf "\"%s\"" s

(* To print c "(" arg with the function pr ")" *)
let print c pr arg =
  Format.printf "@[<hv 0>%s(@," c;
  pr arg;
  Format.printf ")@]"

(* to print a list between "[" "]" *)

let rec print_end_list f = function
  | [] ->
      Format.printf "]@]"
  | x :: l ->
      Format.printf ";@ ";
      f x;
      print_end_list f l

let print_list f = function
  | [] ->
      Format.printf "[]"
  | x :: l ->
      Format.printf "@[<hv 2>[ ";
      f x;
      print_end_list f l


(* To print a subparagraph *)
let print_sub_paragraph = function
  | CamlCode s -> print "CamlCode" print_string s;
  | LexCode s  -> print "LexCode"  print_string s;
  | YaccCode s -> print "YaccCode" print_string s

(* To print a paragraph *)
let print_paragraph = function
  | Documentation (_,_,s) ->
      print "Documentation" print_string s
  | RawLaTeX (s) ->
      print "RawLaTeX" print_string s
  | Code (i,s) ->
      Format.printf "Code(%d,@ %s)" i s
  | LexYaccCode (i,spl) ->
      Format.printf "@[<hv 5>LexYaccCode(%d,@ " i;
      print_list print_sub_paragraph spl;
      Format.printf ")@]"

(* To print a section *)
let print_raw_section { sec_contents = sc; sec_beg = sb } =
  Format.printf "@[<hv 2>{ sec_beg = %d ;@ sec_contents =@ " sb ;
  print_list print_paragraph sc;
  Format.printf ";@ }@]"

(* To print a [Web.content] *)
let print_content { content_file = c;
		    content_name = cn;
		    content_contents  = rl } =
  Format.printf "@[<hv 2>{ content_file = \"%s\" ;@ content_name = \"%s\" ;@ contents_contents =@ " c cn ;
  print_list print_raw_section rl ;
  Format.printf ";@ }@]"

(* To print a [Web.file] *)
let print_file f =
  begin
    match f with
      | Implem c -> print "Implem" print_content c
      | Interf c -> print "Interf" print_content c
      | Lex c    -> print "Lex"    print_content c
      | Yacc c   -> print "Yacc"   print_content c
      | Other s  -> print "Other"  print_string s
  end;
  Format.printf "@."



(*i*)


(*s Options of the engine. *)

let index = ref true

let web = ref true

let extern_defs = ref false

let latex_options = ref ""

let add_latex_option s =
  if !latex_options = "" then
    latex_options := s
  else
    latex_options := !latex_options ^ "," ^ s


(*s Construction of the global index. *)

let index_file = function
  | Implem i -> cross_implem i.content_file i.content_name
  | Interf i -> cross_interf i.content_file i.content_name
  | Yacc i -> cross_yacc i.content_file i.content_name
  | Lex i -> cross_lex i.content_file i.content_name
  | Other _ -> ()

let build_index l = List.iter index_file l


(*s The locations tables. \label{counters} *)

module Smap = Map.Make(struct type t = string let compare = compare end)

let sec_locations = ref Smap.empty
let code_locations = ref Smap.empty

let add_loc table file ((_,s) as loc) =
  let l = try Smap.find file !table with Not_found -> [(0,s)] in
  table := Smap.add file (loc :: l) !table

let add_par_loc =
  let par_counter = ref 0 in
  fun f p -> match p with
    | Code (l,_) ->
	incr par_counter;
	add_loc code_locations f (l,!par_counter)
    | LexYaccCode (l,_) ->
	incr par_counter;
	add_loc code_locations f (l,!par_counter)
    | Documentation _ -> ()
    | RawLaTeX _ -> ()

let add_sec_loc =
  let sec_counter = ref 0 in
  fun f s ->
    incr sec_counter;
    add_loc sec_locations f (s.sec_beg,!sec_counter);
    (*i
    Printf.eprintf "section %d starts at character %d of file %s\n"
      !sec_counter s.sec_beg f;
    i*)
    List.iter (add_par_loc f) s.sec_contents

let add_file_loc it =
  List.iter (add_sec_loc it.content_file) it.content_contents

let locations_for_a_file = function
  | Implem i -> add_file_loc i
  | Interf i -> add_file_loc i
  | Lex i -> add_file_loc i
  | Yacc i -> add_file_loc i
  | Other _ -> ()

let find_where w =
  let rec lookup = function
    | [] -> raise Not_found
    | (l,n) :: r -> if w.w_loc >= l then ((w.w_filename,l),n) else lookup r
  in
  let table = if !web then !sec_locations else !code_locations in
  lookup (Smap.find w.w_filename table)


(*s Printing of the index. *)

(*s Alphabetic order for index entries.
    To sort index entries, we define the following order relation
    [alpha_string]. It puts symbols first (identifiers that do not begin
    with a letter), and symbols are compared using Caml's generic order
    relation. For real identifiers, we first normalize them by translating
    lowercase characters to uppercase ones and by removing all the accents,
    and then we use Caml's comparison.
 *)

let norm_char c = match Char.uppercase_ascii c with
  | '\192'..'\198' -> 'A'
  | '\199' -> 'C'
  | '\200'..'\203' -> 'E'
  | '\204'..'\207' -> 'I'
  | '\209' -> 'N'
  | '\210'..'\214' | '\216' -> 'O'
  | '\217'..'\220' -> 'U'
  | '\221' -> 'Y'
  | c -> c

let norm_string s =
  let u = Bytes.of_string s in
  for i = 0 to String.length s - 1 do
    Bytes.set u i (norm_char s.[i])
  done;
  Bytes.to_string u

let alpha_string s1 s2 =
  match what_is_first_char s1, what_is_first_char s2 with
    | Symbol, Symbol -> compare s1 s2
    | Symbol, _ -> -1
    | _, Symbol -> 1
    | _,_ -> compare (norm_string s1) (norm_string s2)

let order_entry e1 e2 =
  let c = alpha_string e1.e_name e2.e_name in
  if c <> 0 then
    c
  else
    compare e1.e_type e2.e_type

(*s The following function collects all the index entries and sort them
    using [alpha_string], returning a list. *)

module Idset = Set.Make(struct type t = index_entry let compare = compare end)

let all_entries () =
  let s = Idmap.fold (fun x _ s -> Idset.add x s) !used Idset.empty in
  let s = Idmap.fold (fun x _ s -> Idset.add x s) !defined s in
  List.sort order_entry (Idset.elements s)


(*s When we are in \LaTeX\ style, an index entry only consists in two lists
    of labels, which are treated by the \LaTeX\ macro \verb!\ocwrefindexentry!.
    When we are in WEB style, we can do a bit better, replacing a list
    like 1,2,3,4,7,8,10 by 1--4,7,8,10, as in usual \LaTeX\ indexes.
    The following function [intervals] is used to group together the lists
    of at least three consecutive integers.
 *)

let intervals l =
  let rec group = function
    | (acc, []) -> List.rev acc
    | (Interval (s1,(_,n2)) :: acc, (f,n) :: rem) when n = succ n2 ->
	group (Interval (s1,(f,n)) :: acc, rem)
    | ((Single _)::(Single (f1,n1))::acc, (f,n)::rem) when n = n1 + 2 ->
	group (Interval ((f1,n1),(f,n)) :: acc, rem)
    | (acc, (f,n) :: rem) ->
	group ((Single (f,n)) :: acc, rem)
  in
  group ([],l)

let make_label_name (f,n) = f ^ ":" ^ (string_of_int n)

let label_list l =
  List.map (fun x -> make_label_name (fst x)) l

let elem_map f = function
  | Single x -> Single (f x)
  | Interval (x,y) -> Interval (f x, f y)

let web_list l =
  let l = intervals l in
  List.map (elem_map (fun x -> make_label_name (fst x))) l


(*s Printing one index entry.
    The function call [(list_in_table id t)] collects all the sections for
    the identifier [id] in the table [t], using the function [find_where],
    and sort the result thanks to the counter which was associated to each
    new location (see section~\ref{counters}). It also removes the duplicates
    labels.
  *)

let rec uniquize = function
  | [] | [_] as l -> l
  | x :: (y :: r as l) -> if x = y then uniquize l else x :: (uniquize l)

let map_succeed_nf f l =
  let rec map = function
    | [] -> []
    | x :: l -> try (f x) :: (map l) with Not_found -> map l
  in
  map l

let list_in_table id t =
  try
    let l = Whereset.elements (Idmap.find id t) in
    let l = map_succeed_nf find_where l in
    let l = List.sort (fun x x' -> compare (snd x) (snd x')) l in
    uniquize l
  with Not_found ->
    []

let entry_type_name = function
  | Value | Constructor -> ""
  | Field      -> "(field)"
  | Label      -> "(label)"
  | Type       -> "(type)"
  | Exception  -> "(exn)"
  | Module     -> "(module)"
  | ModuleType -> "(sig)"
  | Class      -> "(class)"
  | Method     -> "(method)"
  | LexParseRule -> "(camllex parsing rule)"
  | RegExpr      -> "(camllex regexpr)"
  | YaccNonTerminal -> "(camlyacc non-terminal)"
  | YaccTerminal    -> "(camlyacc token)"

let print_one_entry id =
  let def = list_in_table id !defined in
  if !extern_defs || def <> [] then begin
    let use = list_in_table id !used in
    let s = id.e_name in
    let t = entry_type_name id.e_type in
    if !web then
      output_index_entry s t (web_list def) (web_list use)
    else
      output_raw_index_entry s t (label_list def) (label_list use)
  end

(*s Then printing the index is just iterating [print_one_entry] on all the
    index entries, given by [(all_entries())]. *)

let print_index () =
  begin_index ();
  List.iter print_one_entry (all_entries());
  end_index ()


(*s Pretty-printing of the document. *)

let rec pretty_print_sub_paragraph = function
  | CamlCode(s) ->
       pretty_print_caml_subpar s
  | YaccCode(s) ->
       pretty_print_yacc_subpar s
  | LexCode(s)  ->
       pretty_print_lex_subpar s


let pretty_print_paragraph is_first_paragraph is_last_paragraph f = function
  | Documentation (b,n,s) ->
      end_code ();
      pretty_print_doc is_first_paragraph (b,n,s);
      end_line()  (*i ajout Dorland-Muller i*)
  | RawLaTeX s ->
     end_code ();
     output_string s;
     end_line()
  | Code (l,s) ->
      if l > 0 then output_label (make_label_name (f,l));
      begin_code_paragraph ();
      begin_code ();
      pretty_print_code is_last_paragraph s
  | LexYaccCode (l,s) ->
      if l > 0 then output_label (make_label_name (f,l));
      begin_code_paragraph ();
      begin_code ();
      List.iter pretty_print_sub_paragraph s;
      end_code_paragraph is_last_paragraph

let pretty_print_section first f s =
  if !web then begin_section ();
  if first && s.sec_beg > 0 then output_label (make_label_name (f,0));
  output_label (make_label_name (f,s.sec_beg));
  let rec loop is_first_paragraph = function
    | [] ->
	()
    | [ p ] ->
	pretty_print_paragraph is_first_paragraph true f p
    | p :: rest ->
	pretty_print_paragraph is_first_paragraph false f p;
	loop false rest
  in
  loop true s.sec_contents;
  end_code ()

let pretty_print_sections f = function
  | [] -> ()
  | s :: r ->
      pretty_print_section true f s;
      List.iter (pretty_print_section false f) r

let pretty_print_content output_header content =
  reset_pretty();
  output_header content.content_name;
  pretty_print_sections content.content_file content.content_contents

let pretty_print_file = function
  | Implem i -> pretty_print_content output_module i
  | Interf i -> pretty_print_content output_interface i
  | Lex i -> pretty_print_content output_lexmodule i
  | Yacc i -> pretty_print_content output_yaccmodule i
  | Other f -> output_file f


(*s Production of the document. We proceed in three steps:
    \begin{enumerate}
    \item Build the index;
    \item Pretty-print of files;
    \item Printing of the index.
    \end{enumerate}
 *)

let produce_document l =
  (*i
    List.iter print_file l;
    i*)
  List.iter locations_for_a_file l;
  build_index l;
  latex_header !latex_options;
  List.iter pretty_print_file l;
  if !index then print_index ();
  latex_trailer ();
  close_output ()
