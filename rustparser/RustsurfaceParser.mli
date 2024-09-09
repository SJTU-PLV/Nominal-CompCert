
(* The type of tokens. *)

type token = 
  | WHILE
  | WHERE
  | UINT8
  | UINT64
  | UINT32
  | UINT16
  | TRUE
  | SUBS
  | STR_LITERAL of (string)
  | STRUCT
  | SEMICOLON
  | RPAREN
  | RETURN
  | REF
  | RBRACE
  | RARROWW
  | RARROW
  | RANGLE
  | PREF
  | ORIGIN of (string)
  | OR
  | NOT
  | NE
  | MUT
  | MATCH
  | LPAREN
  | LOOP
  | LET
  | LE
  | LBRACE
  | LANGLE
  | INT8
  | INT64
  | INT32
  | INT16
  | INT of (int)
  | IN
  | IF
  | ID of (string)
  | GE
  | FN
  | FLOAT64
  | FLOAT32
  | FALSE
  | EQ
  | EOF
  | ENUM
  | ELSE
  | DOT
  | DIV
  | CONTINUE
  | COMMA
  | COLON2
  | COLON
  | CASE
  | BREAK
  | BOX
  | BOOL
  | ASTERISK
  | ASSIGN
  | AS
  | AND
  | ADD

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog_eof: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Rustsurface.prog_item list)

module MenhirInterpreter : sig
  
  (* The incremental API. *)
  
  include MenhirLib.IncrementalEngine.INCREMENTAL_ENGINE
    with type token = token
  
end

(* The entry point(s) to the incremental API. *)

module Incremental : sig
  
  val prog_eof: Lexing.position -> (Rustsurface.prog_item list) MenhirInterpreter.checkpoint
  
end
