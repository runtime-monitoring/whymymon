(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Term : sig

  type t = Var of string | Const of Dom.t [@@deriving compare, sexp_of, hash]

  type comparator_witness

  val unvar: t -> string

  val unconst: t -> Dom.t

  val is_var: t -> bool

  val is_const: t -> bool

  val comparator: (t, comparator_witness) Comparator.t

  val fv_list: t list -> string list

  val equal: t -> t -> bool

  val to_string: t -> string

  val value_to_string: t -> string

  val list_to_string: t list -> string

  val list_to_json_string: t list -> string

end

module Sig : sig

  type props = { arity: int; ntconsts: (string * Dom.tt) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  val table: (string, props) Hashtbl.t

  val add: string -> (string * Dom.tt) list -> unit

  val vars: string -> string list

  val var_tt: string -> Dom.tt

  val print_table: unit -> unit

end

val check_terms: string -> Term.t list -> Term.t list
