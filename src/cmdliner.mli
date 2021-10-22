(*---------------------------------------------------------------------------
   Copyright (c) 2011 The cmdliner programmers. All rights reserved.
   Distributed under the ISC license, see terms at the end of the file.
  ---------------------------------------------------------------------------*)

(** Declarative definition of command line interfaces.

    Consult the {{!page-tutorial}tutorial}, details about the supported
    {{!page-cli}command line syntax} and {{!page-examples}examples} of
    use.

    Open the module to use it, it defines only three modules in your
    scope. *)

(** Man page specification.

    Man page generation is automatically handled by [Cmdliner],
    consult the {{!page-tutorial.manual}details}.

    The {!Manpage.block} type is used to define a man page's
    content. It's a good idea to follow the
    {{!Manpage.standard_sections}standard} manual page structure.

   {b References.}
   {ul
   {- [man-pages(7)], {{:http://man7.org/linux/man-pages/man7/man-pages.7.html}
      {e Conventions for writing Linux man pages}}.}} *)
module Manpage : sig

  (** {1:man Man pages} *)

  type block =
    [ `S of string | `P of string | `Pre of string | `I of string * string
    | `Noblank | `Blocks of block list ]
  (** The type for a block of man page text.

      {ul
      {- [`S s] introduces a new section [s], see the
         {{!standard_sections}standard section names}.}
      {- [`P t] is a new paragraph with text [t].}
      {- [`Pre t] is a new preformatted paragraph with text [t].}
      {- [`I (l,t)] is an indented paragraph with label
         [l] and text [t].}
      {- [`Noblank] suppresses the blank line introduced between two blocks.}
      {- [`Blocks bs] splices the blocks [bs].}}

      Except in [`Pre], whitespace and newlines are not significant
      and are all collapsed to a single space. All block strings
      support the {{!page-tutorial.doclang}documentation markup language}.*)

  val escape : string -> string
  (** [escape s] escapes [s] so that it doesn't get interpreted by the
      {{!page-tutorial.doclang}documentation markup language}. *)

  type title = string * int * string * string * string
  (** The type for man page titles. Describes the man page
      [title], [section], [center_footer], [left_footer], [center_header]. *)

  type t = title * block list
  (** The type for a man page. A title and the page text as a list of blocks. *)

  type xref =
    [ `Main | `Cmd of string | `Tool of string | `Page of string * int ]
  (** The type for man page cross-references.
      {ul
      {- [`Main] refers to the man page of the program itself.}
      {- [`Cmd cmd] refers to the man page of the program's [cmd]
         command (which must exist).}
      {- [`Tool bin] refers to the command line tool named [bin].}
      {- [`Page (name, sec)] refers to the man page [name(sec)].}} *)

  (** {1:standard_sections Standard section names and content}

      The following are standard man page section names, roughly ordered
      in the order they conventionally appear. See also
      {{:http://man7.org/linux/man-pages/man7/man-pages.7.html}[man man-pages]}
      for more elaborations about what sections should contain. *)

  val s_name : string
  (** The [NAME] section. This section is automatically created by
      [Cmdliner] for your. *)

  val s_synopsis : string
  (** The [SYNOPSIS] section. By default this section is automatically
      created by [Cmdliner] for you, unless it is the first section of
      your term's man page, in which case it will replace it with yours. *)

  val s_description : string
  (** The [DESCRIPTION] section. This should be a description of what
      the tool does and provide a little bit of usage and
      documentation guidance. *)

  val s_commands : string
  (** The [COMMANDS] section. By default subcommands get listed here. *)

  val s_arguments : string
  (** The [ARGUMENTS] section. By default positional arguments get
      listed here. *)

  val s_options : string
  (** The [OPTIONS] section. By default options and flag arguments get
      listed here. *)

  val s_common_options : string
  (** The [COMMON OPTIONS] section. For programs with multiple commands
      a section that can be used to gather options common to all commands. *)

  val s_exit_status : string
  (** The [EXIT STATUS] section. By default term status exit codes
      get listed here. *)

  val s_environment : string
  (** The [ENVIRONMENT] section. By default environment variables get
      listed here. *)

  val s_environment_intro : block
  (** [s_environment_intro] is the introduction content used by cmdliner
      when it creates the {!s_environment} section. *)

  val s_files : string
  (** The [FILES] section. *)

  val s_bugs : string
  (** The [BUGS] section. *)

  val s_examples : string
  (** The [EXAMPLES] section. *)

  val s_authors : string
  (** The [AUTHORS] section. *)

  val s_see_also : string
  (** The [SEE ALSO] section. *)

  (** {1:output Output}

    The {!print} function can be useful if the client wants to define
    other man pages (e.g. to implement a help command). *)

  type format = [ `Auto | `Pager | `Plain | `Groff ]
  (** The type for man page output specification.
      {ul
      {- [`Auto], formats like [`Pager] or [`Plain] whenever the [TERM]
         environment variable is [dumb] or unset.}
      {- [`Pager], tries to write to a discovered pager, if that fails
         uses the [`Plain] format.}
      {- [`Plain], formats to plain text.}
      {- [`Groff], formats to groff commands.}} *)

  val print :
    ?errs:Format.formatter ->
    ?subst:(string -> string option) -> format -> Format.formatter -> t -> unit
  (** [print ~errs ~subst fmt ppf page] prints [page] on [ppf] in the
      format [fmt]. [subst] can be used to perform variable
      substitution,(defaults to the identity). [errs] is used to print
      formatting errors, it defaults to {!Format.err_formatter}. *)
end

(** Terms.

    A term is evaluated by a program to produce a {{!Term.result}result},
    which can be turned into an {{!Term.exits}exit status}. A term made of terms
    referring to {{!Arg}command line arguments} implicitly defines a
    command line syntax. *)
module Term : sig

  (** {1:terms Terms} *)

  type +'a t
  (** The type for terms evaluating to values of type 'a. *)

  val const : 'a -> 'a t
  (** [const v] is a term that evaluates to [v]. *)

  (**/**)
  val pure : 'a -> 'a t
  [@@ocaml.deprecated "use Term.const instead."]
  (** @deprecated use {!const} instead. *)

  val man_format : Manpage.format t
  [@@ocaml.deprecated "use Arg.man_format instead."]
  (** @deprecated Use {!Arg.man_format} instead. *)
  (**/**)

  val ( $ ) : ('a -> 'b) t -> 'a t -> 'b t
  (** [f $ v] is a term that evaluates to the result of applying
      the evaluation of [v] to the one of [f]. *)

  val app : ('a -> 'b) t -> 'a t -> 'b t
  (** [app] is {!($)}. *)

  (** {1 Interacting with Cmdliner's evaluation} *)

  type 'a ret =
    [ `Help of Manpage.format * string option
    | `Error of (bool * string)
    | `Ok of 'a ]
  (** The type for command return values. See {!val-ret}. *)

  val ret : 'a ret t -> 'a t
  (** [ret v] is a term whose evaluation depends on the case
      to which [v] evaluates. With :
      {ul
      {- [`Ok v], it evaluates to [v].}
      {- [`Error (usage, e)], the evaluation fails and [Cmdliner] prints
         the error [e] and the term's usage if [usage] is [true].}
      {- [`Help (format, name)], the evaluation fails and [Cmdliner] prints the
         term's man page in the given [format] (or the man page for a
         specific [name] term in case of multiple term evaluation).}}   *)

  val term_result : ?usage:bool -> ('a, [`Msg of string]) result t -> 'a t
  (** [term_result ~usage t] evaluates to
      {ul
      {- [`Ok v] if [t] evaluates to [Ok v]}
      {- [`Error `Term] with the error message [e] and usage shown according
         to [usage] (defaults to [false]), if [t] evaluates to
         [Error (`Msg e)].}} *)

  val cli_parse_result : ('a, [`Msg of string]) result t -> 'a t
  (** [cli_parse_result t] is a term that evaluates to:
      {ul
      {- [`Ok v] if [t] evaluates to [Ok v].}
      {- [`Error `Parse] with the error message [e]
         if [t] evaluates to [Error (`Msg e)].}} *)

  val main_name : string t
  (** [main_name] is a term that evaluates to the "main" term's name. *)

  val choice_names : string list t
  (** [choice_names] is a term that evaluates to the names of the terms
      to choose from. *)

  val with_used_args : 'a t -> ('a * string list) t
  (** [with_used_args t] is a term that evaluates to [t] tupled
      with the arguments from the command line that where used to
      evaluate [t]. *)

  (** {1:tinfo Term information}

      Term information defines the name and man page of a term.
      For simple evaluation this is the name of the program and its
      man page. For multiple term evaluation, this is
      the name of a command and its man page. *)

  type exit_info
  (** The type for exit status information. *)

  val exit_info : ?docs:string -> ?doc:string -> ?max:int -> int -> exit_info
  (** [exit_info ~docs ~doc min ~max] describe the range of exit
      statuses from [min] to [max] (defaults to [min]). [doc] is the
      man page information for the statuses, defaults to ["undocumented"].
      [docs] is the title of the man page section in which the statuses
      will be listed, it defaults to {!Manpage.s_exit_status}.

      In [doc] the {{!page-tutorial.doclang}documentation markup language}
      can be used with following variables:
      {ul
      {- [$(status)], the value of [min].}
      {- [$(status_max)], the value of [max].}
      {- The variables mentioned in {!val-info}}} *)

  val default_exits : exit_info list
  (** [default_exits] is information for exit status {!exit_status_success}
      added to {!default_error_exits}. *)

  val default_error_exits : exit_info list
  (** [default_error_exits] is information for exit statuses
      {!exit_status_cli_error} and {!exit_status_internal_error}. *)

  type env_info
  (** The type for environment variable information. *)

  val env_info : ?docs:string -> ?doc:string -> string -> env_info
  (** [env_info ~docs ~doc var] describes an environment variable
      [var]. [doc] is the man page information of the environment
      variable, defaults to ["undocumented"]. [docs] is the title of
      the man page section in which the environment variable will be
      listed, it defaults to {!Cmdliner.Manpage.s_environment}.

      In [doc] the {{!page-tutorial.doclang}documentation markup language}
      can be used with following variables:
      {ul
      {- [$(env)], the value of [var].}
      {- The variables mentioned in {!val-info}}} *)

  type info
  (** The type for term information. *)

  val info :
    ?man_xrefs:Manpage.xref list -> ?man:Manpage.block list ->
    ?envs:env_info list -> ?exits:exit_info list -> ?sdocs:string ->
    ?docs:string -> ?doc:string -> ?version:string -> string -> info
  (** [info sdocs man docs doc version name] is a term information
      such that:
      {ul
      {- [name] is the name of the program or the command.}
      {- [version] is the version string of the program, ignored
         for commands.}
      {- [doc] is a one line description of the program or command used
         for the [NAME] section of the term's man page. For commands this
         description is also used in the list of commands of the main
         term's man page.}
      {- [docs], only for commands, the title of the section of the main
         term's man page where it should be listed (defaults to
         {!Manpage.s_commands}).}
      {- [sdocs] defines the title of the section in which the
         standard [--help] and [--version] arguments are listed
         (defaults to {!Manpage.s_options}).}
      {- [exits] is a list of exit statuses that the term evaluation
         may produce.}
      {- [envs] is a list of environment variables that influence
         the term's evaluation.}
      {- [man] is the text of the man page for the term.}
      {- [man_xrefs] are cross-references to other manual pages. These
         are used to generate a {!Manpage.s_see_also} section.}}
      [doc], [man], [envs] support the {{!page-tutorial.doclang}documentation
      markup language} in which the following variables are recognized:
      {ul
      {- [$(tname)] the term's name.}
      {- [$(mname)] the main term's name.}} *)

  val name : info -> string
  (** [name ti] is the name of the term information. *)

 (** {1:evaluation Evaluation} *)

  type 'a result =
    [ `Ok of 'a | `Error of [`Parse | `Term | `Exn ] | `Version | `Help ]
  (** The type for evaluation results.
      {ul
      {- [`Ok v], the term evaluated successfully and [v] is the result.}
      {- [`Version], the version string of the main term was printed
       on the help formatter.}
      {- [`Help], man page about the term was printed on the help formatter.}
      {- [`Error `Parse], a command line parse error occurred and was
         reported on the error formatter.}
      {- [`Error `Term], a term evaluation error occurred and was reported
         on the error formatter (see {!Term.val-ret}').}
      {- [`Error `Exn], an exception [e] was caught and reported
         on the error formatter (see the [~catch] parameter of {!eval}).}} *)

  val eval :
    ?help:Format.formatter -> ?err:Format.formatter -> ?catch:bool ->
    ?env:(string -> string option) -> ?argv:string array -> ('a t * info) ->
    'a result
  (** [eval help err catch argv (t,i)]  is the evaluation result
      of [t] with command line arguments [argv] (defaults to {!Sys.argv}).

      If [catch] is [true] (default) uncaught exceptions
      are intercepted and their stack trace is written to the [err]
      formatter.

      [help] is the formatter used to print help or version messages
      (defaults to {!Format.std_formatter}). [err] is the formatter
      used to print error messages (defaults to {!Format.err_formatter}).

      [env] is used for environment variable lookup, the default
      uses {!Sys.getenv}. *)

  val eval_choice :
    ?help:Format.formatter -> ?err:Format.formatter -> ?catch:bool ->
    ?env:(string -> string option) -> ?argv:string array ->
    'a t * info -> ('a t * info) list -> 'a result
  (** [eval_choice help err catch argv (t,i) choices] is like {!eval}
      except that if the first argument on the command line is not an option
      name it will look in [choices] for a term whose information has this
      name and evaluate it.

      If the command name is unknown an error is reported. If the name
      is unspecified the "main" term [t] is evaluated. [i] defines the
      name and man page of the program. *)

  val eval_peek_opts :
    ?version_opt:bool -> ?env:(string -> string option) ->
    ?argv:string array -> 'a t -> 'a option * 'a result
  (** [eval_peek_opts version_opt argv t] evaluates [t], a term made
      of optional arguments only, with the command line [argv]
      (defaults to {!Sys.argv}). In this evaluation, unknown optional
      arguments and positional arguments are ignored.

      The evaluation returns a pair. The first component is
      the result of parsing the command line [argv] stripped from
      any help and version option if [version_opt] is [true] (defaults
      to [false]). It results in:
      {ul
      {- [Some _] if the command line would be parsed correctly given the
         {e partial} knowledge in [t].}
      {- [None] if a parse error would occur on the options of [t]}}

      The second component is the result of parsing the command line
      [argv] without stripping the help and version options. It
      indicates what the evaluation would result in on [argv] given
      the partial knowledge in [t] (for example it would return
      [`Help] if there's a help option in [argv]). However in
      contrasts to {!eval} and {!eval_choice} no side effects like
      error reporting or help output occurs.

      {b Note.} Positional arguments can't be peeked without the full
      specification of the command line: we can't tell apart a
      positional argument from the value of an unknown optional
      argument.  *)

  (** {1:exits Turning evaluation results into exit codes}

      {b Note.} If you are using the following functions to handle
      the evaluation result of a term you should add {!default_exits} to
      the term's information {{!val-info}[~exits]} argument.

      {b WARNING.} You should avoid status codes strictly greater than 125
      as those may be used by
      {{:https://www.gnu.org/software/bash/manual/html_node/Exit-Status.html}
       some} shells. *)

  val exit_status_success : int
  (** [exit_status_success] is 0, the exit status for success. *)

  val exit_status_cli_error : int
  (** [exit_status_cli_error] is 124, an exit status for command line
      parsing errors. *)

  val exit_status_internal_error : int
  (** [exit_status_internal_error] is 125, an exit status for unexpected
      internal errors. *)

  val exit_status_of_result : ?term_err:int -> unit result -> int
  (** [exit_status_of_result ~term_err r] is an [exit(3)] status
      code determined from [r] as follows:
      {ul
      {- {!exit_status_success} if [r] is one of [`Ok ()], [`Version], [`Help]}
      {- [term_err] if [r] is [`Error `Term], [term_err] defaults to [1].}
      {- {!exit_status_cli_error} if [r] is [`Error `Parse]}
      {- {!exit_status_internal_error} if [r] is [`Error `Exn]}} *)

  val exit_status_of_status_result : ?term_err:int -> int result -> int
  (** [exit_status_of_status_result] is like {!exit_status_of_result}
      except for [`Ok n] where [n] is used as the status exit code. *)

  val exit : ?term_err:int -> unit result -> unit
  (** [exit ~term_err r] is
      [Stdlib.exit @@ exit_status_of_result ~term_err r] *)

  val exit_status : ?term_err:int -> int result -> unit
  (** [exit_status ~term_err r] is
      [Stdlib.exit @@ exit_status_of_status_result ~term_err r] *)
end

(** Terms for command line arguments.

    This module provides functions to define terms that evaluate
    to the arguments provided on the command line.

    Basic constraints, like the argument type or repeatability, are
    specified by defining a value of type {!Arg.t}. Further constraints can
    be specified during the {{!Arg.argterms}conversion} to a term. *)
module Arg : sig

(** {1:argconv Argument converters}

    An argument converter transforms a string argument of the command
    line to an OCaml value. {{!converters}Predefined converters}
    are provided for many types of the standard library. *)

  type 'a parser = string -> [ `Ok of 'a | `Error of string ]
  (** The type for argument parsers.

      @deprecated Use a parser with [('a, [ `Msg of string]) result] results
      and {!conv}. *)

  type 'a printer = Format.formatter -> 'a -> unit
  (** The type for converted argument printers. *)

  type 'a conv = 'a parser * 'a printer
  (** The type for argument converters.

      {b WARNING.} This type will become abstract in the next
      major version of cmdliner, use {!val:conv} or {!pconv}
      to construct values of this type. *)

  type 'a converter = 'a conv
  (** @deprecated Use the {!type:conv} type via the {!val:conv} and {!pconv}
      functions. *)

  val conv :
    ?docv:string -> (string -> ('a, [`Msg of string]) result) * 'a printer ->
    'a conv
  (** [converter ~docv (parse, print)] is an argument converter
      parsing values with [parse] and printing them with
      [print]. [docv] is a documentation meta-variable used in the
      documentation to stand for the argument value, defaults to
      ["VALUE"]. *)

  val conv' :
    ?docv:string -> (string -> ('a, string) result) * 'a printer ->
    'a conv
  (** [conv'] is like {!conv} but the [Error] case has an unlabelled
      string. *)

  val pconv :
    ?docv:string -> 'a parser * 'a printer -> 'a conv
  (** [pconv] is like {!converter}, but uses a deprecated {!parser}
      signature. *)

  val conv_parser : 'a conv -> (string -> ('a, [`Msg of string]) result)
  (** [conv_parser c] 's [c]'s parser. *)

  val conv_printer : 'a conv -> 'a printer
  (** [conv_printer c] is [c]'s printer. *)

  val conv_docv : 'a conv -> string
  (** [conv_docv c] is [c]'s documentation meta-variable.

      {b WARNING.} Currently always returns ["VALUE"] in the future
      will return the value given to {!val-conv} or {!val-pconv}. *)

  val parser_of_kind_of_string :
    kind:string -> (string -> 'a option) ->
    (string -> ('a, [`Msg of string]) result)
  (** [parser_of_kind_of_string ~kind kind_of_string] is an argument
      parser using the [kind_of_string] function for parsing and [kind]
      to report errors (e.g. could be ["an integer"] for an [int] parser.). *)

  val some : ?none:string -> 'a conv -> 'a option conv
  (** [some none c] is like the converter [c] except it returns
      [Some] value. It is used for command line arguments
      that default to [None] when absent. [none] is what to print to
      document the absence (defaults to [""]). *)

(** {1:arginfo Arguments and their information}

    Argument information defines the man page information of an
    argument and, for optional arguments, its names. An environment
    variable can also be specified to read the argument value from
    if the argument is absent from the command line and the variable
    is defined. *)

  type env = Term.env_info
  (** The type for environment variables and their documentation. *)

  val env_var : ?docs:string -> ?doc:string -> string -> env
  (** [env_var docs doc var] is an environment variables [var]. [doc]
      is the man page information of the environment variable, the
      {{!page-tutorial.doclang}documentation markup language} with the variables
      mentioned in {!val-info} be used; it defaults to ["See option
      $(opt)."].  [docs] is the title of the man page section in which
      the environment variable will be listed, it defaults to
      {!Manpage.s_environment}. *)

  type 'a t
  (** The type for arguments holding data of type ['a]. *)

  type info
  (** The type for information about command line arguments. *)

  val info :
    ?docs:string -> ?docv:string -> ?doc:string -> ?env:env -> string list ->
    info
  (** [info docs docv doc env names] defines information for
      an argument.
      {ul
      {- [names] defines the names under which an optional argument
         can be referred to. Strings of length [1] (["c"]) define
         short option names (["-c"]), longer strings (["count"])
         define long option names (["--count"]). [names] must be empty
         for positional arguments.}
      {- [env] defines the name of an environment variable which is
         looked up for defining the argument if it is absent from the
         command line. See {{!page-cli.envlookup}environment variables} for
         details.}
      {- [doc] is the man page information of the argument.
         The {{!page-tutorial.doclang}documentation language} can be used and
         the following variables are recognized:
         {ul
         {- ["$(docv)"] the value of [docv] (see below).}
         {- ["$(opt)"], one of the options of [names], preference
            is given to a long one.}
         {- ["$(env)"], the environment var specified by [env] (if any).}}
         {{!doc_helpers}These functions} can help with formatting argument
         values.}
      {- [docv] is for positional and non-flag optional arguments.
         It is a variable name used in the man page to stand for their value.}
      {- [docs] is the title of the man page section in which the argument
         will be listed. For optional arguments this defaults
         to {!Manpage.s_options}. For positional arguments this defaults
         to {!Manpage.s_arguments}. However a positional argument is only
         listed if it has both a [doc] and [docv] specified.}} *)

  val ( & ) : ('a -> 'b) -> 'a -> 'b
  (** [f & v] is [f v], a right associative composition operator for
      specifying argument terms. *)

(** {1:optargs Optional arguments}

    The information of an optional argument must have at least
    one name or [Invalid_argument] is raised. *)

  val flag : info -> bool t
  (** [flag i] is a [bool] argument defined by an optional flag
      that may appear {e at most} once on the command line under one of
      the names specified by [i]. The argument holds [true] if the
      flag is present on the command line and [false] otherwise. *)

  val flag_all : info -> bool list t
  (** [flag_all] is like {!flag} except the flag may appear more than
      once. The argument holds a list that contains one [true] value per
      occurrence of the flag. It holds the empty list if the flag
      is absent from the command line. *)

  val vflag : 'a -> ('a * info) list -> 'a t
  (** [vflag v \[v]{_0}[,i]{_0}[;...\]] is an ['a] argument defined
      by an optional flag that may appear {e at most} once on
      the command line under one of the names specified in the [i]{_k}
      values. The argument holds [v] if the flag is absent from the
      command line and the value [v]{_k} if the name under which it appears
      is in [i]{_k}.

      {b Note.} Environment variable lookup is unsupported for
      for these arguments. *)

  val vflag_all : 'a list -> ('a * info) list -> 'a list t
  (** [vflag_all v l] is like {!vflag} except the flag may appear more
      than once. The argument holds the list [v] if the flag is absent
      from the command line. Otherwise it holds a list that contains one
      corresponding value per occurrence of the flag, in the order found on
      the command line.

      {b Note.} Environment variable lookup is unsupported for
      for these arguments. *)

  val opt : ?vopt:'a -> 'a conv -> 'a -> info -> 'a t
  (** [opt vopt c v i] is an ['a] argument defined by the value of
      an optional argument that may appear {e at most} once on the command
      line under one of the names specified by [i]. The argument holds
      [v] if the option is absent from the command line. Otherwise
      it has the value of the option as converted by [c].

      If [vopt] is provided the value of the optional argument is itself
      optional, taking the value [vopt] if unspecified on the command line. *)

  val opt_all : ?vopt:'a -> 'a conv -> 'a list -> info -> 'a list t
  (** [opt_all vopt c v i] is like {!opt} except the optional argument may
      appear more than once. The argument holds a list that contains one value
      per occurrence of the flag in the order found on the command line.
      It holds the list [v] if the flag is absent from the command line. *)

  (** {1:posargs Positional arguments}

      The information of a positional argument must have no name
      or [Invalid_argument] is raised. Positional arguments indexing
      is zero-based.

      {b Warning.} The following combinators allow to specify and
      extract a given positional argument with more than one term.
      This should not be done as it will likely confuse end users and
      documentation generation. These over-specifications may be
      prevented by raising [Invalid_argument] in the future. But for now
      it is the client's duty to make sure this doesn't happen. *)

  val pos : ?rev:bool -> int -> 'a conv -> 'a -> info -> 'a t
  (** [pos rev n c v i] is an ['a] argument defined by the [n]th
      positional argument of the command line as converted by [c].
      If the positional argument is absent from the command line
      the argument is [v].

      If [rev] is [true] (defaults to [false]), the computed
      position is [max-n] where [max] is the position of
      the last positional argument present on the command line. *)

  val pos_all : 'a conv -> 'a list -> info -> 'a list t
  (** [pos_all c v i] is an ['a list] argument that holds
      all the positional arguments of the command line as converted
      by [c] or [v] if there are none. *)

  val pos_left :
    ?rev:bool -> int -> 'a conv -> 'a list -> info -> 'a list t
  (** [pos_left rev n c v i] is an ['a list] argument that holds
      all the positional arguments as converted by [c] found on the left
      of the [n]th positional argument or [v] if there are none.

      If [rev] is [true] (defaults to [false]), the computed
      position is [max-n] where [max] is the position of
      the last positional argument present on the command line. *)

  val pos_right :
    ?rev:bool -> int -> 'a conv -> 'a list -> info -> 'a list t
  (** [pos_right] is like {!pos_left} except it holds all the positional
      arguments found on the right of the specified positional argument. *)

  (** {1:argterms Arguments as terms} *)

  val value : 'a t -> 'a Term.t
  (** [value a] is a term that evaluates to [a]'s value. *)

  val required : 'a option t -> 'a Term.t
  (** [required a] is a term that fails if [a]'s value is [None] and
      evaluates to the value of [Some] otherwise. Use this for required
      positional arguments (it can also be used for defining required
      optional arguments, but from a user interface perspective this
      shouldn't be done, it is a contradiction in terms). *)

  val non_empty : 'a list t -> 'a list Term.t
  (** [non_empty a] is term that fails if [a]'s list is empty and
      evaluates to [a]'s list otherwise. Use this for non empty lists
      of positional arguments. *)

  val last : 'a list t -> 'a Term.t
  (** [last a] is a term that fails if [a]'s list is empty and evaluates
      to the value of the last element of the list otherwise. Use this
      for lists of flags or options where the last occurrence takes precedence
      over the others. *)

  (** {1:predef Predefined arguments} *)

  val man_format : Manpage.format Term.t
  (** [man_format] is a term that defines a [--man-format] option and
      evaluates to a value that can be used with {!Manpage.print}. *)

  (** {1:converters Predefined converters} *)

  val bool : bool conv
  (** [bool] converts values with {!bool_of_string}. *)

  val char : char conv
  (** [char] converts values by ensuring the argument has a single char. *)

  val int : int conv
  (** [int] converts values with {!int_of_string}. *)

  val nativeint : nativeint conv
  (** [nativeint] converts values with {!Nativeint.of_string}. *)

  val int32 : int32 conv
  (** [int32] converts values with {!Int32.of_string}. *)

  val int64 : int64 conv
  (** [int64] converts values with {!Int64.of_string}. *)

  val float : float conv
  (** [float] converts values with {!float_of_string}. *)

  val string : string conv
  (** [string] converts values with the identity function. *)

  val enum : (string * 'a) list -> 'a conv
  (** [enum l p] converts values such that unambiguous prefixes of string names
      in [l] map to the corresponding value of type ['a].

      {b Warning.} The type ['a] must be comparable with {!Stdlib.compare}.

      @raise Invalid_argument if [l] is empty. *)

  val file : string conv
  (** [file] converts a value with the identity function and
      checks with {!Sys.file_exists} that a file with that name exists. *)

  val dir : string conv
  (** [dir] converts a value with the identity function and checks
      with {!Sys.file_exists} and {!Sys.is_directory}
      that a directory with that name exists. *)

  val non_dir_file : string conv
  (** [non_dir_file] converts a value with the identity function and checks
      with {!Sys.file_exists} and {!Sys.is_directory}
      that a non directory file with that name exists. *)

  val list : ?sep:char -> 'a conv -> 'a list conv
  (** [list sep c] splits the argument at each [sep] (defaults to [','])
      character and converts each substrings with [c]. *)

  val array : ?sep:char -> 'a conv -> 'a array conv
  (** [array sep c] splits the argument at each [sep] (defaults to [','])
      character and converts each substring with [c]. *)

  val pair : ?sep:char -> 'a conv -> 'b conv -> ('a * 'b) conv
  (** [pair sep c0 c1] splits the argument at the {e first} [sep] character
      (defaults to [',']) and respectively converts the substrings with
      [c0] and [c1]. *)

  val t2 : ?sep:char -> 'a conv -> 'b conv -> ('a * 'b) conv
  (** {!t2} is {!pair}. *)

  val t3 : ?sep:char -> 'a conv ->'b conv -> 'c conv -> ('a * 'b * 'c) conv
  (** [t3 sep c0 c1 c2] splits the argument at the {e first} two [sep]
      characters (defaults to [',']) and respectively converts the
      substrings with [c0], [c1] and [c2]. *)

  val t4 :
    ?sep:char -> 'a conv -> 'b conv -> 'c conv -> 'd conv ->
    ('a * 'b * 'c * 'd) conv
  (** [t4 sep c0 c1 c2 c3] splits the argument at the {e first} three [sep]
      characters (defaults to [',']) respectively converts the substrings
      with [c0], [c1], [c2] and [c3]. *)

  (** {1:doc_helpers Documentation formatting helpers} *)

  val doc_quote : string -> string
  (** [doc_quote s] quotes the string [s]. *)

  val doc_alts : ?quoted:bool -> string list -> string
  (** [doc_alts alts] documents the alternative tokens [alts]
      according the number of alternatives. If [quoted] is:
      {ul
      {- [None], the tokens are enclosed in manpage markup directives
         to render them in bold (manpage convention).}
      {- [Some true], the tokens are quoted with {!doc_quote}.}
      {- [Some false], the tokens are written as is}}
      The resulting string can be used in sentences of
      the form ["$(docv) must be %s"].

      @raise Invalid_argument if [alts] is the empty list.  *)

  val doc_alts_enum : ?quoted:bool -> (string * 'a) list -> string
  (** [doc_alts_enum quoted alts] is [doc_alts quoted (List.map fst alts)]. *)
end

(*---------------------------------------------------------------------------
   Copyright (c) 2011 The cmdliner programmers

   Permission to use, copy, modify, and/or distribute this software for any
   purpose with or without fee is hereby granted, provided that the above
   copyright notice and this permission notice appear in all copies.


   THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
   WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
   MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
   ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
   WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
   ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
   OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
  ---------------------------------------------------------------------------*)
