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

module Polarity = struct

  type t = SAT | VIO

  let invert = function
    | SAT -> VIO
    | VIO -> SAT

  let of_pref = function
    | Argument.Preference.Satisfaction -> SAT
    | Violation -> VIO

end

let do_neg (p_opt: Proof.t option) (pol: Polarity.t) =
  match p_opt with
  | None -> None
  | Some p -> (match p, pol with
               | S sp, SAT -> Some (Proof.V (VNeg sp))
               | S _ , VIO -> None
               | V _ , SAT -> None
               | V vp, VIO -> Some (S (SNeg vp)))

let do_and (p1_opt: Proof.t option) (p2_opt: Proof.t option) (pol: Polarity.t) : Proof.t option =
  match p1_opt, p2_opt with
  | Some p1, Some p2 -> Proof.Size.minp_list
                          (match p1, p2, pol with
                           | S sp1, S sp2, SAT -> [Proof.S (SAnd (sp1, sp2))]
                           | S _ , V vp2, VIO -> [V (VAndR (vp2))]
                           | V vp1, S _, VIO -> [V (VAndL (vp1))]
                           | V vp1, V vp2, VIO -> [(V (VAndL (vp1))); (V (VAndR (vp2)))]
                           | _ -> [])
  | _ -> None


let do_or (p1_opt: Proof.t option) (p2_opt: Proof.t option) (pol: Polarity.t) : Proof.t option =
  match p1_opt, p2_opt with
  | Some p1, Some p2 -> Proof.Size.minp_list
                          (match p1, p2, pol with
                           | S sp1, S sp2, SAT -> [(S (SOrL (sp1))); (S (SOrR(sp2)))]
                           | S sp1, V _, SAT -> [S (SOrL (sp1))]
                           | V _ , S sp2, SAT -> [S (SOrR (sp2))]
                           | V vp1, V vp2, VIO -> [V (VOr (vp1, vp2))]
                           | _ -> [])
  | _ -> None

let do_imp (p1_opt: Proof.t option) (p2_opt: Proof.t option) (pol: Polarity.t) : Proof.t option =
  match p1_opt, p2_opt with
  | Some p1, Some p2 -> Proof.Size.minp_list
                          (match p1, p2, pol with
                           | S _, S sp2, SAT -> [S (SImpR sp2)]
                           | S sp1, V vp2, VIO -> [V (VImp (sp1, vp2))]
                           | V vp1, S sp2, SAT -> [S (SImpL vp1); S (SImpR sp2)]
                           | V vp1, V _, SAT -> [S (SImpL vp1)]
                           | _ -> [])
  | _ -> None

let do_iff (p1_opt: Proof.t option) (p2_opt: Proof.t option) (pol: Polarity.t) : Proof.t option =
  match p1_opt, p2_opt with
  | Some p1, Some p2 -> (match p1, p2, pol with
                         | S sp1, S sp2, SAT -> Some (S (SIffSS (sp1, sp2)))
                         | S sp1, V vp2, VIO -> Some (V (VIffSV (sp1, vp2)))
                         | V vp1, S sp2, VIO -> Some (V (VIffVS (vp1, sp2)))
                         | V vp1, V vp2, SAT -> Some (S (SIffVV (vp1, vp2)))
                         | _ -> None)

let do_exists_leaf x tc = function
  | Some p -> (match p with
               | Proof.S sp -> Some (Proof.S (SExists (x, Dom.tt_default tc, sp)))
               | V vp -> Some (V (VExists (x, Part.trivial vp))))
  | None -> None

let do_exists_node x tc part =
  if Part.exists part Proof.opt_isS then
    (let sats = Part.filter part Proof.opt_isS in
     (Part.values (Part.map2_dedup Proof.opt_equal sats (fun (s, p) ->
                       match p with
                       | Some (S sp) -> (let witness = Setc.some_elt tc s in
                                  (Setc.Finite (Set.of_list (module Dom) [witness]),
                                   Some (Proof.S (Proof.SExists (x, Setc.some_elt tc s, sp)))))
                       | Some (V vp) -> raise (Invalid_argument "found V proof in S partition")
                       | None -> raise (Invalid_argument "found None in Some partition")))))
  else [Some (V (Proof.VExists (x, Part.map_dedup Proof.v_equal part Proof.opt_unV)))]

let do_forall_leaf x tc = function
  | Some p -> (match p with
               | Proof.S sp -> Some (Proof.S (SForall (x, Part.trivial sp)))
               | V vp -> Some (Proof.V (VForall (x, Dom.tt_default tc, vp))))
  | None -> None

let do_forall_node x tc part =
  if Part.for_all part Proof.opt_isS then
    [Some (Proof.S (SForall (x, Part.map_dedup Proof.s_equal part Proof.opt_unS)))]
  else
    (let vios = Part.filter part (fun p -> Proof.opt_isV p) in
     (Part.values (Part.map2_dedup Proof.opt_equal vios (fun (s, p) ->
                       match p with
                       | Some (V vp) -> let witness = Setc.some_elt tc s in
                                        (Setc.Finite (Set.of_list (module Dom) [witness]),
                                         Some (Proof.V (Proof.VForall (x, Setc.some_elt tc s, vp))))
                       | Some (S sp) -> raise (Invalid_argument "found S proof in V partition")
                       | None -> raise (Invalid_argument "found None in Some partition")))))

let print_maps maps =
  Stdio.print_endline "> Map:";
  List.iter maps ~f:(fun map -> Map.iteri map ~f:(fun ~key:k ~data:v ->
                                    Stdio.printf "%s -> %s\n" (Term.to_string k) (Dom.to_string v)))

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

let rec pdt_of tp r trms (vars: string list) maps = match vars with
  | [] -> if List.is_empty maps then Pdt.Leaf (Proof.V (VPred (tp, r, trms)))
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
           ; pol: Polarity.t
           ; tp: timepoint
           ; expl: Expl.t }

end


let explain trace v pol tp f =
  let stop vars expl = match vars, expl with
    | _ -> failwith "not yet" in
  let rec eval vars (pol: Polarity.t) tp (f: Formula.t) = match f with
    | TT ->
       (match pol with
        | SAT -> Pdt.Leaf (Some (Expl.Proof.S (STT tp)))
        | VIO -> Pdt.Leaf None)
    | FF ->
       (match pol with
        | SAT -> Pdt.Leaf None
        | VIO -> Pdt.Leaf (Some (Expl.Proof.V (VFF tp))))
    | EqConst (x, d) ->
       let l1 = Pdt.Leaf (Some (Proof.S (SEqConst (tp, x, d)))) in
       let l2 = Pdt.Leaf (Some (Proof.V (VEqConst (tp, x, d)))) in
       (match pol, Map.find v x with
        | SAT, Some d' when Dom.equal d d' -> l1
        | VIO, Some d' when not (Dom.equal d d') -> l2
        | SAT, None ->
           Pdt.Node (x, Part.of_list [(Setc.Complement (Set.of_list (module Dom) [d]), l2);
                                      (Setc.Finite (Set.of_list (module Dom) [d]), l1)])
        | VIO, None ->
           Pdt.Node (x, Part.of_list [(Setc.Complement (Set.of_list (module Dom) [d]), l1);
                                      (Setc.Finite (Set.of_list (module Dom) [d]), l2)]))
    | Predicate (r, trms) ->
       (* Replace trms with values coming from variable assignment v *)
       let trms_subst = List.map trms ~f:(fun trm -> if Pred.Term.is_var trm then
                                                       (match Map.find v (Pred.Term.unvar trm) with
                                                        | None -> trm
                                                        | Some d -> Const d)
                                                     else trm) in
       let db = Set.filter (snd (Array.get trace tp)) ~f:(fun evt -> String.equal r (fst(evt))) in
       let maps = Set.fold db ~init:[] ~f:(fun acc evt -> match_terms trms_subst (snd evt)
                                                            (Map.empty (module String)) :: acc) in
       let maps' = List.map (List.filter maps ~f:(fun map_opt -> match map_opt with
                                                                 | None -> false
                                                                 | Some(map) -> not (Map.is_empty map)))
                     ~f:(fun map_opt -> Option.value_exn map_opt) in
       let fvs = Set.of_list (module String) (Pred.Term.fv_list trms_subst) in
       let vars = List.filter vars ~f:(fun x -> Set.mem fvs x) in
       Pdt.add_somes (pdt_of tp r trms vars maps')
    | Neg f ->
       let expl = eval vars pol tp f in
       Pdt.apply1_reduce Proof.opt_equal vars
         (fun p_opt -> do_neg p_opt pol) expl
    | And (f1, f2) ->
       let expl1 = eval vars pol tp f1 in
       let expl2 = eval vars pol tp f2 in
       Pdt.apply2_reduce Proof.opt_equal vars
         (fun p1_opt p2_opt -> (do_and p1_opt p2_opt pol)) expl1 expl2
    | Or (f1, f2) ->
       let expl1 = eval vars pol tp f1 in
       let expl2 = eval vars pol tp f2 in
       Pdt.apply2_reduce Proof.opt_equal vars
         (fun p1_opt p2_opt -> (do_or p1_opt p2_opt pol)) expl1 expl2
    | Imp (f1, f2) ->
       let expl1 = eval vars pol tp f1 in
       let expl2 = eval vars pol tp f2 in
       Pdt.apply2_reduce Proof.opt_equal vars
         (fun p1_opt p2_opt -> (do_imp p1_opt p2_opt pol)) expl1 expl2
    | Iff (f1, f2) ->
       let expl1 = eval vars pol tp f1 in
       let expl2 = eval vars pol tp f2 in
       Pdt.apply2_reduce Proof.opt_equal vars
         (fun p1_opt p2_opt -> (do_iff p1_opt p2_opt pol)) expl1 expl2
    | Exists (x, tc, f) ->
       let expl = eval vars pol tp f in
       Pdt.hide_reduce Proof.opt_equal (vars @ [x])
         (fun p_opt -> do_exists_leaf x tc p_opt)
         (fun part -> Proof.Size.minp_list_somes (do_exists_node x tc part)) expl
    | Forall (x, tc, f) ->
       let expl = eval vars pol tp f in
       Pdt.hide_reduce Proof.opt_equal (vars @ [x])
         (fun p_opt -> do_forall_leaf x tc p_opt)
         (fun part -> Proof.Size.minp_list_somes (do_forall_node x tc part)) expl
    | Prev (i, f) -> (match pol with
                      | SAT -> Pdt.Leaf None
                      | VIO -> Pdt.Leaf None)
    | Next (i, f) -> (match pol with
                      | SAT -> Pdt.Leaf None
                      | VIO -> Pdt.Leaf None)
    | Once (i, f) -> (match pol with
                      | SAT -> Pdt.Leaf None
                      | VIO -> Pdt.Leaf None)
    | Eventually (i, f) -> (match pol with
                            | SAT -> Pdt.Leaf None
                            | VIO -> Pdt.Leaf None)
    | Historically (i, f) -> (match pol with
                              | SAT -> Pdt.Leaf None
                              | VIO -> Pdt.Leaf None)
    | Always (i, f) -> (match pol with
                        | SAT -> Pdt.Leaf None
                        | VIO -> Pdt.Leaf None)
    | Since (i, f1, f2) -> (match pol with
                            | SAT -> since_sat vars i f1 f2 tp []
                            | VIO -> Pdt.Leaf None)
    | Until (i, f1, f2) -> (match pol with
                            | SAT -> Pdt.Leaf None
                            | VIO -> Pdt.Leaf None)
  and since_sat vars i f1 f2 tp expl1s =
    (* let continue_alphas_sat i f1 f2 tp alphas_sat = *)
    (*   (match eval vars SAT tp f1 with *)
    (*    | Some expl1 -> *)
    (*       (\* Found alpha satisfaction within the interval *\) *)
    (*       (match Hashtbl.find h_tp_ts (tp - 1) with *)
    (*        | Some ts' -> let ts = Hashtbl.find_exn h_tp_ts tp in *)
    (*                      since_sat vars (Interval.sub (ts - ts') i) *)
    (*                        f1 f2 (tp - 1) (expl1 :: alphas_sat) *)
    (*        | None -> None) *)
    (*    | None -> None) in *)

    (* if Interval.mem 0 i then *)
    (*   (let expl1 = eval vars SAT tp f1 in *)
    (*    let expl2 = eval vars SAT tp f2 in *)
    (*    let result = Pdt.apply3_reduce Proof.equal vars *)
    (*                   (fun sp1_opt sp2_opt sp1s -> *)
    (*                     match sp1_opt with *)
    (*                     | None -> *)
    (*                     | Some (sp1) -> Proof.s_append sp sp1) *)
    (*                   expl1 expl2 expl1s in *)

    (*    match result with *)
    (*    | *)
    (* else  *)Pdt.Leaf None

    (*    | Some expl2 -> *)
    (*       (\* Found beta satisfaction within the interval *\) *)
    (*       let ssince_expl = Pdt.apply1_reduce Proof.equal vars *)
    (*                           (fun sp2 -> Proof.S (SSince (Proof.unS sp2, Fdeque.empty))) expl2 in *)
    (*       Some (List.fold alphas_sat ~init:ssince_expl ~f:(fun expl alpha_sat -> *)
    (*                 Pdt.apply2_reduce Proof.equal vars *)
    (*                   (fun sp sp1 -> Proof.s_append sp sp1) *)
    (*                   expl alpha_sat)) *)
    (*    | None -> continue_alphas_sat i f1 f2 tp alphas_sat) *)
    (* else continue_alphas_sat i f1 f2 tp alphas_sat *)
  and since_vio vars i f1 f2 cur_tp tp betas_vio = Pdt.Leaf None
    (* let continue_betas_vio i f1 f2 tp betas_vio = *)
    (*   (match eval vars VIO tp f2 with *)
    (*    | Some expl2 -> *)
    (*       (\* Found beta violation within the interval *\) *)
    (*       (match Hashtbl.find h_tp_ts (tp - 1) with *)
    (*        | Some ts' -> let ts = Hashtbl.find_exn h_tp_ts tp in *)
    (*                      since_vio vars (Interval.sub (ts - ts') i) *)
    (*                        f1 f2 (tp - 1) (expl2 :: betas_vio) *)
    (*        | None -> None) *)
    (*    | None -> None) in *)
    (* The interval has not started yet *)
    (* if not (Interval.mem 0 i) && Int.equal tp 0 then *)
    (*   Some (Pdt.Leaf (Proof.V (VSinceOut cur_tp))) *)
    (* else *)
    (*   (if Interval.mem 0 i then *)
    (*      (match eval vars VIO tp f1 with *)
    (*       | Some expl1 -> *)
    (*          (\* Found alpha violation within the interval *\) *)
    (*          let vsince_expl = Pdt.apply1_reduce Proof.equal vars *)
    (*                              (fun vp1 -> Proof.V (VSince (cur_tp, Proof.unV vp1, Fdeque.empty))) expl1 in *)
    (*          Some (List.fold betas_vio ~init:vsince_expl ~f:(fun expl beta_vio -> *)
    (*                    Pdt.apply2_reduce Proof.equal vars *)
    (*                      (fun vp vp2 -> Proof.v_append vp vp2) *)
    (*                      expl beta_vio)) *)
    (*       | None -> *)
    (*          (\* Continue collecting beta violations *\) *)
    (*          let x = () in None) *)
    (*    else None) *)
  and until_sat i f1 f2 tp = Pdt.Leaf None in
  eval [] pol tp f

(* Spawn thread to execute WhyMyMon somewhere in this function *)
let read ~domain_mgr r_source r_sink end_of_stream mon f trace pol mode =
  let vars = Set.elements (Formula.fv f) in
  let buf = Eio.Buf_read.of_flow r_source ~initial_size:100 ~max_size:1_000_000 in
  let stop = ref false in
  while true do
    let line = Eio.Buf_read.line buf in
    traceln "Read emonitor line: %s" line;
    (* traceln "Trace size: %d" (Fdeque.length !trace); *)
    if String.equal line "Stop" then raise Exit;
    let (ts, assignments) = Emonitor.to_ts_assignments mon vars line in
    traceln "%s" (Etc.string_list_to_string ~sep:"\n" (List.map assignments ~f:Assignment.to_string));
    let tp = Array.length trace - 1 in
    List.iter assignments ~f:(fun v ->
        let expl = explain trace v pol tp f in
        match mode with
        | Argument.Mode.Unverified -> Out.Plain.print (Explanation ((ts, tp), expl))
        (* | Verified -> let (b, _, _) = List.hd_exn (Checker_interface.check (Array.to_list trace) f [expl]) in *)
        (*               Out.Plain.print (ExplanationCheck ((ts, tp), expl, b)) *)
        | LaTeX -> Out.Plain.print (ExplanationLatex ((ts, tp), expl, f))
        (* | Debug -> let (b, c_e, c_trace) = List.hd_exn (Checker_interface.check (Array.to_list trace) f [expl]) in *)
        (*            let paths = List.hd_exn (Checker_interface.false_paths (Array.to_list c_trace) f [expl]) in *)
        (*            Out.Plain.print (ExplanationCheckDebug ((ts, tp), expl, b, c_e, c_trace, paths)) *)
        | DebugVis -> ());
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
                      trace := Array.append !trace [|(pb.ts, pb.db)|];
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
      let trace = ref [||]  in
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
                       read ~domain_mgr r_source r_sink end_of_stream mon f !trace (Polarity.of_pref pref) mode)
          ];
      with Exit -> Stdio.printf "Reached the end of the log file.\n"
    );
