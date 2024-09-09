(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Etc

val to_assignments: Argument.Monitor.t -> string list -> string -> Assignment.t list

val write_line: Argument.Monitor.t -> timestamp * Db.t -> string

val args: Argument.Monitor.t -> mon_path:string -> ?sig_path:string -> f_path:string -> string list
