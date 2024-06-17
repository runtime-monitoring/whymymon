(*******************************************************************)
(*     This is part of DuoMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Stdio

(* TODO: Rewrite this using functors/first-class modules to distinguish monitors *)

module Monpoly = struct

  (* @1308477599 (time point 3): ("Alice",163) ("Charlie",152) ("Charlie",163) *)
  let parse vars lines =


end

let feed (mon: Argument.Monitor.t) out_c ts db =
  (match mon with
   | MonPoly -> Out_channel.output_string out_c ("@" ^ (Int.to_string ts) ^ Db.to_monpoly db)
   | VeriMon -> failwith "missing"
   | DejaVu -> failwith "missing"
   | TimelyMon -> failwith "missing");
  Caml.flush out_c

let read (mon: Argument.Monitor.t) in_c =
  let lines = In_channel.input_lines in_c in
  match mon with
  | MonPoly -> List.fold lines ~init:Monpoly.parse
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"

let start (mon: Argument.Monitor.t) mon_path sig_path f_path = match mon with
  | MonPoly -> Core_unix.open_process (mon_path ^ "-sig " ^ sig_path ^ " -formula " ^ f_path)
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"
