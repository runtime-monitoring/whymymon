(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

module Monitor : sig

  type t = MonPoly | VeriMon | DejaVu | TimelyMon

  val of_string: string -> t

  val to_lowercase_string: t -> string

  val to_string: t -> string

end

module Preference : sig

  type t = Satisfaction | Violation

  val of_string: string -> t

  val to_string: t -> string

end

module Mode : sig

  type t = Unverified | Verified | LaTeX | Debug | DebugVis

  val of_string: string -> t

  val to_string: t -> string

end
