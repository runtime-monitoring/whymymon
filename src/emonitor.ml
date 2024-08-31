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
let write_line (mon: Argument.Monitor.t) out_c ts db =
  match mon with
  | MonPoly -> let ev = "@" ^ (Int.to_string ts) ^ " " ^ Db.to_monpoly db in
               Stdio.printf "%s\n" ev;
               Stdlib.flush_all ();
               Out_channel.output_string out_c ev
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"

let read_line (mon: Argument.Monitor.t) vars line =
  match mon with
  | MonPoly -> let (tp, sss) = Emonitor_parser.Monpoly.parse line in
               List.map sss ~f:(fun ss ->
                   let v = List.fold2_exn vars ss ~init:(Assignment.init ()) ~f:(fun v x s ->
                               let d = Dom.string_to_t s (Pred.Sig.var_tt x) in
                               Assignment.add v x d) in
                   Stdio.printf "%s" (Assignment.to_string v); v)
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"

let command (mon: Argument.Monitor.t) ~mon_path ?sig_path ~f_path = match mon with
  | MonPoly -> [mon_path; "-sig " ^ (Option.value_exn sig_path); "-formula " ^ f_path];
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"

let start (mon: Argument.Monitor.t) ~mon_path sig_path f_path vars stdin stdout =
  let buf = Eio.Buf_read.of_flow stdin ~initial_size:100 ~max_size:1_000_000 in
  while true do
    let line = Eio.Buf_read.line buf in
    Eio.traceln "> %s" line;
    Eio.Flow.copy_string (line ^ "\n") stdout
  done
