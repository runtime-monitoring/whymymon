(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio
open Eio.Std

(* TODO: Rewrite this using functors/first-class modules to distinguish monitors *)

(* Example from Eio library *)
(* let cli ~stdin ~stdout = *)
(*   let buf = Eio.Buf_read.of_flow stdin ~initial_size:100 ~max_size:1_000_000 in *)
(*   while true do *)
(*     let line = Eio.Buf_read.line buf in *)
(*     traceln "> %s" line; *)
(*     match line with *)
(*     | "h" | "help" -> Eio.Flow.copy_string "It's just an example\n" stdout *)
(*     | x -> Eio.Flow.copy_string (Fmt.str "Unknown command %S\n" x) stdout *)
(*   done *)

let feed (mon: Argument.Monitor.t) out_c ts db =
  (match mon with
   | MonPoly -> let ev = "@" ^ (Int.to_string ts) ^ " " ^ Db.to_monpoly db in
                Stdio.printf "%s\n" ev;
                Stdlib.flush_all ();
                Out_channel.output_string out_c ev
   | VeriMon -> failwith "missing"
   | DejaVu -> failwith "missing"
   | TimelyMon -> failwith "missing");
  flush out_c

let read (mon: Argument.Monitor.t) in_c vars =
  (* Blocking read, rewrite this with Eio *)
  let line = In_channel.input_line in_c in
  match line with
  | None -> []
  | Some(lines) ->
     (match mon with
      | MonPoly -> List.map [lines] ~f:(fun line ->
                       let (tp, sss) = Emonitor_parser.Monpoly.parse line in
                       List.map sss ~f:(fun ss ->
                           let v = List.fold2_exn vars ss ~init:(Assignment.init ()) ~f:(fun v x s ->
                                       let d = Dom.string_to_t s (Pred.Sig.var_tt x) in
                                       Assignment.add v x d) in
                           Stdio.printf "%s" (Assignment.to_string v); v))
      | VeriMon -> failwith "missing"
      | DejaVu -> failwith "missing"
      | TimelyMon -> failwith "missing")

let start (mon: Argument.Monitor.t) mon_path sig_path f_path = match mon with
  | MonPoly -> Stdio.printf "%s\n" (mon_path ^ " -sig " ^ sig_path ^ " -formula " ^ f_path);
               (* This should be replaced with Eio.Process.run and all stdin/stdout with Flows *)
               Core_unix.open_process (mon_path ^ " -sig " ^ sig_path ^ " -formula " ^ f_path)
  | VeriMon -> failwith "missing"
  | DejaVu -> failwith "missing"
  | TimelyMon -> failwith "missing"

let stop in_c out_c =
  let _ = Core_unix.close_process (in_c, out_c) in ()
