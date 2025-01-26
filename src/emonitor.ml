(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

(* TODO: Rewrite this using functors/first-class modules to distinguish monitors (or maybe not) *)
let to_tpts_assignments (mon: Argument.Monitor.t) vars line =
  match mon with
  | MonPoly
    | VeriMon -> let (tp, ts, sss) = Emonitor_parser.Monpoly.parse line in
                 if List.is_empty sss then (tp, ts, [Assignment.init ()])
                 else
                   (tp, ts, List.map sss ~f:(fun ss ->
                                List.fold2_exn vars ss ~init:(Assignment.init ())
                                  ~f:(fun v x s -> let d = Dom.string_to_t s (Pred.Sig.var_tt x) in
                                                   Assignment.add v x d)))
  | DejaVu -> failwith "missing"

let is_verdict (mon: Argument.Monitor.t) line =
  match mon with
  | MonPoly
    | VeriMon -> String.equal (String.prefix line 1) "@"
  | DejaVu -> failwith "missing"

let parse_prog_tp (mon: Argument.Monitor.t) line =
  match mon with
  | MonPoly
    | VeriMon -> Int.of_string (List.last_exn (String.split line ~on:' '))
  | DejaVu -> failwith "missing"

let write_line (mon: Argument.Monitor.t) (ts, db) =
  match mon with
  | MonPoly
    | VeriMon -> "@" ^ (Int.to_string ts) ^ " " ^ Db.to_monpoly db
  | DejaVu -> failwith "missing"

let args (mon: Argument.Monitor.t) ~mon_path ?sig_path ~f_path =
  match mon with
  | MonPoly -> [mon_path; "-sig"; Option.value_exn sig_path; "-formula"; f_path; "-nonewlastts"];
  | VeriMon -> [mon_path; "-sig"; Option.value_exn sig_path; "-formula"; f_path; "-nonewlastts"; "-verified"];
  | DejaVu -> failwith "missing"
