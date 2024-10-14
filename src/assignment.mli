(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

type t = (string, Dom.t, String.comparator_witness) Map.t

val init: unit -> t

val add: t -> string -> Dom.t -> t

val to_alist: ?key_order:[ `Decreasing | `Increasing ] -> t -> (string * Dom.t) list

val to_string: t -> string
