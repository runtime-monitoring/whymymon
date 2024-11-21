(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type t = SAT | VIO

let invert = function
  | SAT -> VIO
  | VIO -> SAT

let of_pref = function
  | Argument.Preference.Satisfaction -> SAT
  | Violation -> VIO

let to_string = function
  | SAT -> "SAT"
  | VIO -> "VIO"
