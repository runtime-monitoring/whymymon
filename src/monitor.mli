(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module State : sig

  type t

end

val exec: Argument.Monitor.t -> mon_path:string -> ?sig_path:string ->
          formula_file:string -> Stdio.In_channel.t -> Formula.t ->
          Argument.Preference.t -> Argument.Mode.t -> string list ->
          unit
