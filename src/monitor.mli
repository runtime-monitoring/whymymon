(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

module State : sig

  type t

end

val exec: Argument.Mode.t -> string -> Formula.t -> in_channel -> unit

val exec_vis: State.t option -> Formula.t -> string -> (State.t * string)
