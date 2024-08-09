(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc

type t = (string, Dom.t, String.comparator_witness) Map.t

let init () = Map.empty (module String)

let add v x d = match Map.add v ~key:x ~data:d with
  | `Ok v -> v
  | `Duplicate ->
     raise (Invalid_argument (Printf.sprintf "variable %s already has a mapping" x))

let to_string v =
  Map.fold v ~init:"Assignment:\n" ~f:(fun ~key:x ~data:d s ->
      s ^ Printf.sprintf "%s ↦ %s\n" x (Dom.to_string d))
