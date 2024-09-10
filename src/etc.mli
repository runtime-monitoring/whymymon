(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Fdeque = Core.Fdeque

val debug: bool ref

(* Misc *)
type timepoint = int
type timestamp = int

val eat: string -> string -> string
val paren: int -> int -> ('b, 'c, 'd, 'e, 'f, 'g) format6 -> ('b, 'c, 'd, 'e, 'f, 'g) format6
val is_digit: char -> bool

exception Parsing_error of Lexing.position*Lexing.position*string
val parsing_error: Lexing.position -> Lexing.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val lexing_error: Lexing.lexbuf -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val lexbuf_error_msg: Lexing.lexbuf -> string

exception Empty_deque of string
val deque_to_string: string -> (string -> 'a -> string) -> 'a Core.Fdeque.t -> string

val queue_drop: 'a Base.Queue.t -> int -> 'a Base.Queue.t

val list_to_string: string -> (string -> 'a -> string) -> 'a list -> string

val string_list_to_string: sep:string -> string list  -> string

val some_string: unit -> string

val string_list_to_json: string list -> string

val int_list_to_json: int list -> string

val unquote: string -> string

val escape_underscores: string -> string

val fdeque_for_all2_exn: 'a Fdeque.t -> 'b Fdeque.t -> f:('a -> 'b -> bool) -> bool
val fdeque_for_all2: 'a Fdeque.t -> 'b Fdeque.t -> f:('a -> 'b -> bool) -> bool
