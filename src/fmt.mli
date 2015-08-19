(*---------------------------------------------------------------------------
   Copyright (c) 2014 Daniel C. Bünzli. All rights reserved.
   Distributed under the BSD3 license, see license at the end of the file.
   %%NAME%% release %%VERSION%%
  ---------------------------------------------------------------------------*)

(** {!Format} pretty-printer combinators.

    {b References}
    {ul
    {- The required reading {!Format} module
       {{:https://ocaml.org/learn/tutorials/format.html}tutorial}.}}

    {e Release %%VERSION%% - %%MAINTAINER%% } *)

(** {1:formatting Formatting} *)

val pf : Format.formatter ->
  ('a, Format.formatter, unit) Pervasives.format -> 'a
(** [pf] is {!Format.fprintf}. *)

val kpf : (Format.formatter -> 'a) -> Format.formatter ->
  ('b, Format.formatter, unit, 'a) format4 -> 'b
(** [kpf] is {!Format.kfprintf}. *)

val strf : ('a, Format.formatter, unit, string) format4 -> 'a
(** [strf] is {!Format.asprintf}. *)

val kstrf : (string -> 'a) ->
  ('b, Format.formatter, unit, 'a) format4 -> 'b
(** [kstrf] is like {!Format.ksprintf} but handles "%a" directives. *)

(** {1:fmt Standard output formatting} *)

val stdout : Format.formatter
(** [stdout] is the standard output formatter. *)

val stderr : Format.formatter
(** [stderr] is the standard error formatter. *)

val pr : ('a, Format.formatter, unit) format -> 'a
(** [pr] is [pf stdout]. *)

val epr : ('a, Format.formatter, unit) format -> 'a
(** [epr] is [pf stderr]. *)

(** {1 Formatters} *)

type 'a t = Format.formatter -> 'a -> unit
(** The type for formatters of values of type ['a]. *)

val nop : 'a t
(** [nop] formats nothing. *)

val cut : unit t
(** [cut] is {!Format.pp_print_cut}. *)

val sp : unit t
(** [sp] is {!Format.pp_print_space}. *)

val const : 'a t -> 'a -> unit t
(** [const pp_v v] always formats [v] using [pp_v]. *)

val unit : (unit, Format.formatter, unit) Pervasives.format -> unit t
(** [unit fmt] formats a unit value with the format [fmt]. *)

val fmt : ('a, Format.formatter, unit) Pervasives.format ->
  Format.formatter -> 'a
(** [fmt fmt ppf] is [pf ppf fmt]. If [fmt] is used with a single
    non-constant formatting directive, generates a value of type
    {!t}. *)

(** {1:boxes Boxes} *)

val box : ?indent:int -> 'a t -> 'a t
(** [box ~indent pp ppf] wraps [pp] in a horizontal or vertical box. Break
    hints that lead to a new line add [indent] to the current indentation
    (defaults to [0]). *)

val hbox : 'a t -> 'a t
(** [hbox] is like {!box} but is a horizontal box: the line is not split
    in this box (but may be in sub-boxes). *)

val vbox : ?indent:int -> 'a t -> 'a t
(** [vbox] is like {!box} but is a vertical box: every break hint leads
    to a new line which adds [indent] to the current indentation
    (default to [0]). *)

val hvbox : ?indent:int -> 'a t -> 'a t
(** [hvbox] is like {!box} but is either {!hbox} if its fits on
    a single line or {!vbox} otherwise. *)

(** {1:basetypes Base type formatters} *)

val bool : bool t
(** [bool] is {!Format.pp_print_bool}. *)

val int : int t
(** [int] is {!Format.pp_print_int}. *)

val int32 : int32 t
(** [int32 ppf] is [pf ppf "%ld"]. *)

val int64 : int64 t
(** [int64 ppf] is [pf ppf "%Ld"]. *)

val uint32 : int32 t
(** [int32 ppf] is [pf ppf "%lu"]. *)

val uint64 : int64 t
(** [uint64 ppf] is [pf ppf "%Lu"]. *)

val uint : int t
(** [uint ppf] is [pf ppf "%u"]. *)

val float : float t
(** [float ppf] is [pf ppf "%g".] *)

val float_dfrac : int -> float t
(** [float_dfrac d] rounds the float to the [d]th {e decimal}
    fractional digit and formats the result with ["%g"]. Ties are
    rounded towards positive infinity. The result is only defined
    for [0 <= d <= 16]. *)

val float_dsig : int -> float t
(** [pp_float_dsig d] rounds the normalized {e decimal} significand
    of the float to the [d]th decimal fractional digit and formats
    the result with ["%g"]. Ties are rounded towards positive
    infinity. The result is NaN on infinities and only defined for
    [0 <= d <= 16].

    {b Warning.} The current implementation overflows on large [d]
    and floats. *)

val char : char t
(** [char] is {!Format.pp_print_char}. *)

val string : string t
(** [string] is {!Format.pp_print_string}. *)

val buffer : Buffer.t t
(** [buffer] formats a {!Buffer.t} value's current contents. *)

(** {1:polytypes Polymorphic type formatters}

    These formatters give full control to the client over the
    formatting process and do not wrap the formatted structures with
    boxes. Use the {!Dump} module to quickly format values for
    inspection.  *)

val pair : ?sep:unit t -> 'a t -> 'b t -> ('a * 'b) t
(** [pair ~sep pp_fst pp_snd] formats a pair. The first and second
    projection are formatted using [pp_fst] and [pp_snd] and are
    separated by [sep] (defaults to {!cut}). *)

val option : ?none:unit t -> 'a t -> 'a option t
(** [option ~none pp_v] formats an optional value. The [Some] case
    uses [pp_v] and [None] uses [none] (defaults to {!nop}). *)

val list : ?sep:unit t -> 'a t -> 'a list t
(** [list sep pp_v] formats list elements. Each element of the list is
    formatted in order with [pp_v]. Elements are separated by [sep]
    (defaults to {!cut}). If the list is empty, this is {!nop}. *)

val array : ?sep:unit t -> 'a t -> 'a array t
(** [array sep pp_v] formats array elements. Each element of the array
    is formatted in order with [pp_v]. Elements are separated by [sep]
    (defaults to {!cut}). If the array is empty, this is {!nop}. *)

val hashtbl : ?sep:unit t -> ('a * 'b) t -> ('a, 'b) Hashtbl.t t
(** [hashtbl ~sep pp_binding] formats the bindings of a hash
    table. Each binding is formatted with [pp_binding] and bindings
    are separated by [sep] (defaults to {!cut}). If the hash table has
    multiple bindings for a given key, all bindings are formatted,
    with the most recent binding first. If the hash table is empty,
    this is {!nop}. *)

val queue : ?sep:unit t -> 'a t -> 'a Queue.t t
(** [queue ~sep pp_v] formats queue elements. Each element of the
    queue is formatted in least recently added order with
    [pp_v]. Elements are separated by [sep] (defaults to {!cut}). If
    the queue is empty, this is {!nop}. *)

val stack : ?sep:unit t -> 'a t -> 'a Stack.t t
(** [stack ~sep pp_v] formats stack elements. Each element of the
    stack is formatted from top to bottom order with [pp_v].  Elements
    are separated by [sep] (defaults to {!cut}). If the stack is
    empty, this is {!nop}. *)

(** Formatters for inspecting OCaml values.

    Formatters of this module dump OCaml value with little control
    over the representation but with good default box structures and,
    whenever possible, using OCaml syntax. *)
module Dump : sig

  (** {1:polytypes Polymorphic type formatters} *)

  val pair : 'a t -> 'b t -> ('a * 'b) t
  (** [pair pp_fst pp_snd] formats an OCaml pair using [pp_fst] and [pp_snd]
      for the first and second projection. *)

  val option : 'a t -> 'a option t
  (** [option pp_v] formats an OCaml option using [pp_v] for the [Some]
      case. No parentheses are added. *)

  val list : 'a t -> 'a list t
  (** [list pp_v] formats an OCaml list using [pp_v] for the list
      elements. *)

  val array : 'a t -> 'a array t
  (** [array pp_v] formats an OCaml array using [pp_v] for the array
      elements. *)

  val hashtbl : 'a t -> 'b t -> ('a, 'b) Hashtbl.t t
  (** [hashtbl pp_k pp_v] formats an unspecified representation of the
      bindings of a hash table using [pp_k] for the keys and [pp_v]
      for the values. If the hash table has multiple bindings for a
      given key, all bindings are formatted, with the most recent
      binding first. *)

  val queue : 'a t -> 'a Queue.t t
  (** [queue pp_v] formats an unspecified representation of an OCaml
      queue using [pp_v] to format its elements, in least recently added
      order. *)

  val stack : 'a t -> 'a Stack.t t
  (** [stack pp_v] formats an unspecified representation of an OCaml
      stack using [pp_v] to format its elements in top to botttom order. *)
end

(** {1:bracks Brackets} *)

val parens : 'a t -> 'a t
(** [parens pp_v ppf] is [pf "@[<1>(%a)@]" pp_v]. *)

val brackets : 'a t -> 'a t
(** [brackets pp_v ppf] is [pf "@[<1>[%a]@]" pp_v]. *)

val braces : 'a t -> 'a t
(** [brackets pp_v ppf] is [pf "@[<1>{%a}@]" pp_v]. *)

(** {1:text Text and lines} *)

val text : string t
(** [pp_text] formats text by replacing spaces and newlines in the string
    with calls to {!Format.pp_print_space} and {!Format.pp_force_newline}. *)

val lines : string t
(** [pp_lines] formats lines by replacing newlines in the string
    with calls to {!Format.pp_force_newline}. *)

val text_range : ((int * int) * (int * int)) t
(** [text_range] formats a line-column text range according to
    {{:http://www.gnu.org/prep/standards/standards.html#Errors}
    GNU conventions}. *)

val doomed : string t
(** [doomed] should be used for printing a message when reasonable
    assumptions are being violated. The string should be a short
    description of what is going on. *)

(** {1:combi Appending} *)

val append : 'a t -> 'b t -> ('a * 'b) t
(** [append pp_v0 pp_v1 ppf (v0, v1)] is [pp_v0 ppf v0; pp_v1 ppf v1]. *)

val prefix : unit t -> 'a t -> 'a t
(** [prefix pp_pre pp] prefixes [pp] by [pp_pre]. *)

val suffix : unit t -> 'a t -> 'a t
(** [suffix pp_suf pp] suffixes [pp] by [pp_suf]. *)

(** {1 Byte sizes} *)

val byte_size : int t
(** [pp_byte_size] formats a byte size according to its magnitude
    using {{:http://www.bipm.org/en/publications/si-brochure/chapter3.html}
    SI prefixes} up to peta bytes (10{^15}). *)

val bi_byte_size : int t
(** [pp_bi_byte_size] formats a byte size according to its magnitude
    using {{:https://en.wikipedia.org/wiki/Binary_prefix}binary prefixes}
    up to pebi bytes (2{^15}). *)

(** {1:utf8_cond Conditional UTF-8 formatting}

    {b Note.} Since {!Format} is not UTF-8 aware using UTF-8 output
    may derail the pretty printing process. Use the pretty-printers
    from {!Uuseg_string} if you are serious about UTF-8 formatting. *)

val if_utf_8 : 'a t -> 'a t -> 'a t
(** [if_utf_8 pp_u pp] is a t that will use [pp_u] if UTF-8
    output is {{!utf_8_enabled}enabled} and [pp] otherwise. *)

(** {2:utf8_cond Conditional UTF-8 formatting control} *)

val utf_8_enabled : unit -> bool
(** [utf_8_enabled ()] is [true] if UTF-8 pretty-printing is enabled. *)

val set_utf_8_enabled : bool -> unit
(** [set_utf_8_enabled b] sets UTF-8 pretty-printing to [b]. *)

(** {1:styled Styled formatting} *)

type style =
  [ `Bold
  | `Underline
  | `Black
  | `Red
  | `Green
  | `Yellow
  | `Blue
  | `Magenta
  | `Cyan
  | `White
  | `None ]
(** The type for styles. *)

val styled : style -> 'a t -> 'a t
(** [styled style pp] formats according to [pp] but styled with [style]. *)

val styled_string : style -> string t
(** [styled_string style] is [pp_styled style string]. *)

(** {2 Styled formatting control} *)

type style_tags = [ `Ansi | `None ]
(** The type for style tags.
      {ul
      {- [`Ansi], tags the text with
       {{:http://www.ecma-international.org/publications/standards/Ecma-048.htm}
           ANSI escape sequences}.}
      {- [`None], text remains untagged.}} *)

val style_tags : unit -> style_tags
(** [style_tags ()] is the current tag style used by {!Fmt.pp_styled}.
      Initial value is [`None]. *)

val set_style_tags : style_tags -> unit
(** [set_style_tags s] sets the current tag style used by
      {!Fmt.pp_styled}. *)

(** {1:stringconverters Converting with string value converters} *)

val of_to_string : ('a -> string) -> 'a t
(** [of_to_string f ppf v] is [string ppf (f v)]. *)

val to_to_string : 'a t -> 'a -> string
(** [to_to_string pp_v v] is [strf "%a" pp_v v]. *)

(*---------------------------------------------------------------------------
   Copyright (c) 2014 Daniel C. Bünzli.
   All rights reserved.

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions
   are met:

   1. Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

   2. Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

   3. Neither the name of Daniel C. Bünzli nor the names of
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  ---------------------------------------------------------------------------*)
