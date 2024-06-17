(*******************************************************************)
(*     This is part of DuoMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Stdio

let eval (mon: Argument.Monitor.t) db (in_c, out_c) =
  (match mon with
   | MonPoly -> failwith "missing"
   | VeriMon -> failwith "missing"
   | DejaVu -> failwith "missing"
   | TimelyMon -> failwith "missing");
  Caml.flush out_c

let start (mon: Argument.Monitor.t) mon_path sig_path f_path = match mon with
  | MonPoly -> Core_unix.open_process (mon_path ^ "-sig " ^ sig_path ^ " -formula " ^ f_path)
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"
