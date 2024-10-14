(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc
open Checker.Checker

module Checker_trace : sig

  type t = ((string * event_data list) set * nat) list

  val to_string: t -> string

end

module Checker_proof : sig

  type t = ((string, event_data) sproof, (string, event_data) vproof) sum

  val to_string: string -> t -> string

end

val check: (timestamp * (string * Dom.t list, 'a) Base.Set.t) list -> Assignment.t -> Formula.t -> Expl.Proof.t ->
           bool * ((string, event_data) sproof, (string, event_data) vproof) sum * Checker_trace.t
