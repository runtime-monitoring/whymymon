(*******************************************************************)
(*     This is part of DuoMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

type t = (string, Dom.t, String.comparator_witness) Map.t

let parse_from_monpoly vars line =
  let subs = List.map (String.split line ~on:')') ~f:(String.lstrip ~drop:(fun c -> Char.equal c '(')) in
  List.fold subs ~init:(Map.empty (module String)) ~f:(fun map sub ->
      let doms = List.map (String.split sub ~on:',') ~f:(fun s ->
                     if String.is_prefix s ~prefix:"\"" then
                       Dom.Str (String.strip ~drop:(fun c -> Char.equal c '\"') s)
                     else Dom.Int (Int.of_string s)) in
      let map = List.fold2 vars doms ~init:map ~f:(fun map' x d ->
                    Map.add_exn map' ~key:x ~data:d) in
      match map with
      | Ok m -> m
      | Unequal_lengths ->
         raise (Invalid_argument
                  (Printf.sprintf "number of free variables %d does not match MonPoly's output (%s)"
                     (List.length vars) sub)))
