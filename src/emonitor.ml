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
let to_ts_assignments (mon: Argument.Monitor.t) vars line =
  match mon with
  | MonPoly -> let (tp, sss) = Emonitor_parser.Monpoly.parse line in
               (tp, List.map sss ~f:(fun ss ->
                        List.fold2_exn vars ss ~init:(Assignment.init ())
                          ~f:(fun v x s -> let d = Dom.string_to_t s (Pred.Sig.var_tt x) in
                                           Assignment.add v x d)))
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"

let write_line (mon: Argument.Monitor.t) (ts, db) =
  match mon with
  | MonPoly -> "@" ^ (Int.to_string ts) ^ " " ^ Db.to_monpoly db
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"

let args (mon: Argument.Monitor.t) ~mon_path ?sig_path ~f_path =
  match mon with
  | MonPoly -> [mon_path; "-sig"; Option.value_exn sig_path; "-formula"; f_path];
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"
