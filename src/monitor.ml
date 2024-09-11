(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Core
open Etc
open Expl
open Pred
open Eio.Std

type polarity = SAT | VIO

let do_neg (p: Proof.t) pol = match p, pol with
  | S sp, SAT -> Some (Proof.V (VNeg sp))
  | S _ , VIO -> None
  | V _ , SAT -> None
  | V vp, VIO -> Some (S (SNeg vp))

let do_and (p1: Proof.t) (p2: Proof.t) pol : Proof.t option =
  Proof.Size.minp_list
    (match p1, p2, pol with
     | S sp1, S sp2, SAT -> [Proof.S (SAnd (sp1, sp2))]
     | S _ , V vp2, VIO -> [V (VAndR (vp2))]
     | V vp1, S _, VIO -> [V (VAndL (vp1))]
     | V vp1, V vp2, VIO -> [(V (VAndL (vp1))); (V (VAndR (vp2)))]
     | _ -> [])

let do_or (p1: Proof.t) (p2: Proof.t) pol : Proof.t option =
  Proof.Size.minp_list
    (match p1, p2, pol with
     | S sp1, S sp2, SAT -> [(S (SOrL (sp1))); (S (SOrR(sp2)))]
     | S sp1, V _, SAT -> [S (SOrL (sp1))]
     | V _ , S sp2, SAT -> [S (SOrR (sp2))]
     | V vp1, V vp2, VIO -> [V (VOr (vp1, vp2))]
     | _ -> [])

let do_imp (p1: Proof.t) (p2: Proof.t) pol : Proof.t option =
  Proof.Size.minp_list
    (match p1, p2, pol with
     | S _, S sp2, SAT -> [S (SImpR sp2)]
     | S sp1, V vp2, VIO -> [V (VImp (sp1, vp2))]
     | V vp1, S sp2, SAT -> [S (SImpL vp1); S (SImpR sp2)]
     | V vp1, V _, SAT -> [S (SImpL vp1)]
     | _ -> [])

let do_iff (p1: Proof.t) (p2: Proof.t) pol : Proof.t option = match p1, p2, pol with
  | S sp1, S sp2, SAT -> Some (S (SIffSS (sp1, sp2)))
  | S sp1, V vp2, VIO -> Some (V (VIffSV (sp1, vp2)))
  | V vp1, S sp2, VIO -> Some (V (VIffVS (vp1, sp2)))
  | V vp1, V vp2, SAT -> Some (S (SIffVV (vp1, vp2)))
  | _ -> None

let do_exists_leaf x tc = function
  | Proof.S sp -> [Proof.S (SExists (x, Dom.tt_default tc, sp))]
  | V vp -> [Proof.V (VExists (x, Part.trivial vp))]

let do_exists_node x tc part =
  if Part.exists part Proof.isS then
    (let sats = Part.filter part (fun p -> Proof.isS p) in
     (Part.values (Part.map2_dedup Proof.equal sats (fun (s, p) ->
                       match p with
                       | S sp -> (let witness = Setc.some_elt tc s in
                                  (Setc.Finite (Set.of_list (module Dom) [witness]),
                                   Proof.S (Proof.SExists (x, Setc.some_elt tc s, sp))))
                       | V vp -> raise (Invalid_argument "found V proof in S list")))))
  else [V (Proof.VExists (x, Part.map_dedup Proof.v_equal part Proof.unV))]

let do_forall_leaf x tc = function
  | Proof.S sp -> [Proof.S (SForall (x, Part.trivial sp))]
  | V vp -> [Proof.V (VForall (x, Dom.tt_default tc, vp))]

let do_forall_node x tc part =
  if Part.for_all part Proof.isS then
    [Proof.S (SForall (x, Part.map part Proof.unS))]
  else
    (let vios = Part.filter part (fun p -> Proof.isV p) in
     (Part.values (Part.map2_dedup Proof.equal vios (fun (s, p) ->
                       match p with
                       | S sp -> raise (Invalid_argument "found S proof in V list")
                       | V vp -> (let witness = Setc.some_elt tc s in
                                  (Setc.Finite (Set.of_list (module Dom) [witness]),
                                   Proof.V (Proof.VForall (x, Setc.some_elt tc s, vp))))))))

let rec match_terms trms ds map =
  match trms, ds with
  | [], [] -> Some(map)
  | Term.Const c :: trms, d :: ds -> if Dom.equal c d then match_terms trms ds map else None
  | Var x :: trms, d :: ds -> (match match_terms trms ds map with
                               | None -> None
                               | Some(map') -> (match Map.find map' x with
                                                | None -> let map'' = Map.add_exn map' ~key:x ~data:d in Some(map'')
                                                | Some z -> (if Dom.equal d z then Some map' else None)))
  | _, _ -> None

let print_maps maps =
  Stdio.print_endline "> Map:";
  List.iter maps ~f:(fun map -> Map.iteri map ~f:(fun ~key:k ~data:v ->
                                    Stdio.printf "%s -> %s\n" (Term.to_string k) (Dom.to_string v)))

let rec pdt_of tp r trms (vars: string list) maps : Expl.t = match vars with
  | [] -> if List.is_empty maps then Leaf (V (VPred (tp, r, trms)))
          else Leaf (S (SPred (tp, r, trms)))
  | x :: vars ->
     let ds = List.fold maps ~init:[]
                ~f:(fun acc map -> match Map.find map x with
                                   | None -> acc
                                   | Some(d) -> d :: acc) in
     let find_maps d = List.fold maps ~init:[]
                         ~f:(fun acc map -> match Map.find map x with
                                            | None -> acc
                                            | Some(d') -> if Dom.equal d d' then
                                                            map :: acc
                                                          else acc) in
     let part = Part.tabulate_dedup (Pdt.equal Proof.equal) (Set.of_list (module Dom) ds)
                  (fun d -> pdt_of tp r trms vars (find_maps d)) (pdt_of tp r trms vars []) in
     Node (x, part)

let h_tp_ts = Hashtbl.create (module Int)

module State = struct

  type t = { f: Formula.t
           ; pol: polarity
           ; tp: timepoint
           ; expl: Expl.t }

end

let explain vars trace pol tp f =
  let result expl1_opt expl2_opt do_op pol = match expl1_opt, expl2_opt with
    | None, None -> None
    | Some _, None -> None
    | None, Some _ -> None
    | Some expl1, Some expl2 ->
       Pdt.prune_nones (Pdt.apply2_reduce Proof.equal_opt vars
                          (fun p1 p2 -> (do_op p1 p2 pol)) expl1 expl2) in
  let rec eval pol tp (f: Formula.t) = match f with
    | TT -> (match pol with
             | SAT -> Some (Pdt.Leaf (Expl.Proof.S (STT tp)))
             | VIO -> None)
    | FF -> (match pol with
             | SAT -> None
             | VIO -> Some (Pdt.Leaf (Expl.Proof.V (VFF tp))))
    | EqConst (x, d) -> (match pol with
                         | SAT -> None
                         | VIO -> None)
    | Predicate (r, trms) -> (match pol with
                              | SAT -> None
                              | VIO -> None)
    | Neg f -> (match eval pol tp f with
                | None -> None
                | Some expl -> Pdt.prune_nones (Pdt.apply1_reduce Proof.equal_opt vars (fun p -> do_neg p pol) expl))
    | And (f1, f2) -> result (eval pol tp f1) (eval pol tp f2) do_and pol
    | Or (f1, f2) -> result (eval pol tp f1) (eval pol tp f2) do_or pol
    | Imp (f1, f2) -> result (eval pol tp f1) (eval pol tp f2) do_imp pol
    | Iff (f1, f2) -> result (eval pol tp f1) (eval pol tp f2) do_iff pol
    | Exists (x, f) -> (match pol with
                        | SAT -> None
                        | VIO -> None)
    | Forall (x, f) -> (match pol with
                        | SAT -> None
                        | VIO -> None)
    | Prev (i, f) -> (match pol with
                      | SAT -> None
                      | VIO -> None)
    | Next (i, f) -> (match pol with
                      | SAT -> None
                      | VIO -> None)
    | Once (i, f) -> (match pol with
                      | SAT -> None
                      | VIO -> None)
    | Eventually (i, f) -> (match pol with
                            | SAT -> None
                            | VIO -> None)
    | Historically (i, f) -> (match pol with
                              | SAT -> None
                              | VIO -> None)
    | Always (i, f) -> (match pol with
                        | SAT -> None
                        | VIO -> None)
    | Since (i, f1, f2) -> (match pol with
                            | SAT -> since_sat i f1 f2 tp []
                            | VIO -> None)
    | Until (i, f1, f2) -> (match pol with
                            | SAT -> None
                            | VIO -> None)
  and since_sat i f1 f2 tp alphas_sat =
    let continue_alphas_sat i f1 f2 tp alphas_sat =
      (match eval SAT tp f1 with
       | Some expl -> (match Hashtbl.find h_tp_ts (tp - 1) with
                       | Some ts' -> let ts = Hashtbl.find_exn h_tp_ts tp in
                                     since_sat (Interval.sub (ts - ts') i)
                                       f1 f2 (tp - 1) (expl :: alphas_sat)
                       | None -> None)
       | None -> None) in
    if Interval.mem 0 i then
      (match eval SAT tp f2 with
       | Some expl ->
          Some (List.fold alphas_sat ~init:expl ~f:(fun ssince_expl alpha_sat ->
                    Pdt.apply2_reduce Proof.equal vars
                      (fun sp sp1 -> Proof.s_append sp sp1)
                      ssince_expl alpha_sat))
       | None -> continue_alphas_sat i f1 f2 tp alphas_sat)
    else continue_alphas_sat i f1 f2 tp alphas_sat
  and since_vio i f1 f2 tp alphas_sat =
    if Interval.mem 0 i then
      None
    else
      None
  and until_sat i f1 f2 tp =
    if Interval.mem 0 i then
      None
    else
      None in
  eval pol tp f

(* Spawn thread to execute WhyMyMon somewhere in this function *)
let read ~domain_mgr r_source r_sink end_of_stream mon f trace =
  let vars = Set.elements (Formula.fv f) in
  let buf = Eio.Buf_read.of_flow r_source ~initial_size:100 ~max_size:1_000_000 in
  let stop = ref false in
  while true do
    let line = Eio.Buf_read.line buf in
    traceln "Read emonitor line: %s" line;
    (* traceln "Trace size: %d" (Fdeque.length !trace); *)
    if String.equal line "Stop" then raise Exit;
    let assignments = Emonitor.to_assignments mon vars line in
    traceln "%s" (Etc.string_list_to_string ~sep:"\n" (List.map assignments ~f:Assignment.to_string));
    if !end_of_stream then (Eio.Flow.copy_string "Stop\n" r_sink);
    Fiber.yield ()
  done

let write_lines (mon: Argument.Monitor.t) stream w_sink end_of_stream trace =
  let rec step pb_opt =
    match Other_parser.Trace.parse_from_channel stream pb_opt with
    | Finished -> traceln "Reached the end of event stream";
                  end_of_stream := true;
                  Fiber.yield ()
    | Skipped (pb, msg) -> traceln "Skipped time-point due to: %S" msg;
                           Fiber.yield ();
                           step (Some(pb))
    | Processed pb -> traceln "Processed event with time-stamp %d. Sending it to sink." pb.ts;
                      Eio.Flow.copy_string (Emonitor.write_line mon (pb.ts, pb.db)) w_sink;
                      trace := Fdeque.enqueue_back !trace (pb.ts, pb.db);
                      Fiber.yield ();
                      step (Some(pb)) in
  step None

(* sig_path is only passed as a parameter when either MonPoly or VeriMon is the external monitor *)
let exec mon ~mon_path ?sig_path stream f pref mode extra_args =
  let ( / ) = Eio.Path.( / ) in
  Eio_main.run @@ fun env ->
  (* Formula conversion *)
  let f_path = Eio.Stdenv.cwd env / "tmp/f.mfotl" in
  traceln "Saving formula in %a" Eio.Path.pp f_path;
  Eio.Path.save ~create:(`If_missing 0o644) f_path (Formula.convert mon f);
  (* Instantiate process/domain managers *)
  let proc_mgr = Eio.Stdenv.process_mgr env in
  let domain_mgr = Eio.Stdenv.domain_mgr env in
  Switch.run (fun sw ->
      (* source and sink of emonitor's stdin *)
      let w_source, w_sink = Eio.Process.pipe ~sw proc_mgr in
      (* source and sink of emonitor's stdout *)
      let r_source, r_sink = Eio.Process.pipe ~sw proc_mgr in
      (* signals end of stream *)
      let end_of_stream = ref false in
      (* accumulated trace ref *)
      let trace = ref Fdeque.empty in
      try
        Fiber.all
          [ (* Spawn thread with external monitor process *)
            (fun () ->
              let f_realpath = Filename_unix.realpath (Eio.Path.native_exn f_path) in
              let args = Emonitor.args mon ~mon_path ?sig_path ~f_path:f_realpath in
              traceln "Running process with: %s" (Etc.string_list_to_string ~sep:", " args);
              let status = Eio.Process.spawn ~sw ~stdin:w_source ~stdout:r_sink ~stderr:r_sink
                             proc_mgr (args @ extra_args) |> Eio.Process.await in
              match status with
              | `Exited i -> traceln "Process exited with: %d" i
              | `Signaled i -> traceln "Process signaled with: %d" i);
            (* External monitor I/O management *)
            (fun () -> traceln "Writing lines to emonitor's stdin...";
                       write_lines mon stream w_sink end_of_stream trace);
            (fun () -> traceln "Reading lines from emonitor's stdout...";
                       read ~domain_mgr r_source r_sink end_of_stream mon f trace)
          ];
      with Exit -> Stdio.printf "Reached the end of the log file.\n"
    );
