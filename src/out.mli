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
open Checker_interface

module Plain : sig

  type t =
    | Explanation of (timestamp * timepoint) * Expl.t
    | ExplanationCheck of (timestamp * timepoint) * Expl.t * bool
    | ExplanationLatex of (timestamp * timepoint) * Expl.t * Formula.t
    | ExplanationLight of (timestamp * timepoint) * Expl.t
    | ExplanationCheckDebug of (timestamp * timepoint) * Expl.t * bool * Checker_proof.t * Checker_trace.t

  val print: t -> unit

end

(* module Json : sig *)

(*   val table_columns: Formula.t -> string *)

(*   val db: timestamp -> timepoint -> Db.t -> Formula.t -> string *)

(*   val expls: (timepoint, timestamp) Hashtbl.t -> Formula.t -> Expl.t list -> string list *)

(*   val aggregate: string list -> string list -> string -> string *)

(* end *)
