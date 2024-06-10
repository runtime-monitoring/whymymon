(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Core
open Etc
open Expl
open Pred

let do_neg = function
  | Proof.S sp -> Proof.V (VNeg sp)
  | V vp -> S (SNeg vp)

let do_and (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
  | S sp1, S sp2 -> [S (SAnd (sp1, sp2))]
  | S _ , V vp2 -> [V (VAndR (vp2))]
  | V vp1, S _ -> [V (VAndL (vp1))]
  | V vp1, V vp2 -> [(V (VAndL (vp1))); (V (VAndR (vp2)))]

let do_or (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
  | S sp1, S sp2 -> [(S (SOrL (sp1))); (S (SOrR(sp2)))]
  | S sp1, V _ -> [S (SOrL (sp1))]
  | V _ , S sp2 -> [S (SOrR (sp2))]
  | V vp1, V vp2 -> [V (VOr (vp1, vp2))]

let do_imp (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
  | S _, S sp2 -> [S (SImpR sp2)]
  | S sp1, V vp2 -> [V (VImp (sp1, vp2))]
  | V vp1, S sp2 -> [S (SImpL vp1); S (SImpR sp2)]
  | V vp1, V _ -> [S (SImpL vp1)]

let do_iff (p1: Proof.t) (p2: Proof.t) : Proof.t = match p1, p2 with
  | S sp1, S sp2 -> S (SIffSS (sp1, sp2))
  | S sp1, V vp2 -> V (VIffSV (sp1, vp2))
  | V vp1, S sp2 -> V (VIffVS (vp1, sp2))
  | V vp1, V vp2 -> S (SIffVV (vp1, vp2))

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

type polarity = SAT | VIO

module State = struct

  type t = { f: Formula.t
           ; pol: polarity
           ; tp: timepoint
           ; expl: Expl.t }

end

let explain v dbs pol tp f =
  let vars = Set.elements (Formula.fv f) in
  (* What should eval return? A proof tree or a PDT? *)
  let rec eval pol tp (f: Formula.t) = match f with
    | TT -> (match pol with
             | SAT -> ()
             | VIO -> ())
    | FF -> (match pol with
             | SAT -> ()
             | VIO -> ())
    | EqConst (x, d) -> (match pol with
                         | SAT -> ()
                         | VIO -> ())
    | Predicate (r, trms) -> (match pol with
                              | SAT -> ()
                              | VIO -> ())
    | Neg f -> (match pol with
                | SAT -> ()
                | VIO -> ())
    | And (f1, f2) -> (match pol with
                       | SAT -> ()
                       | VIO -> ())
    | Or (f1, f2) -> (match pol with
                      | SAT -> ()
                      | VIO -> ())
    | Imp (f1, f2) -> (match pol with
                       | SAT -> ()
                       | VIO -> ())
    | Iff (f1, f2) -> (match pol with
                       | SAT -> ()
                       | VIO -> ())
    | Exists (x, f) -> (match pol with
                        | SAT -> ()
                        | VIO -> ())
    | Forall (x, f) -> (match pol with
                        | SAT -> ()
                        | VIO -> ())
    | Prev (i, f) -> (match pol with
                      | SAT -> ()
                      | VIO -> ())
    | Next (i, f) -> (match pol with
                      | SAT -> ()
                      | VIO -> ())
    | Once (i, f) -> (match pol with
                      | SAT -> ()
                      | VIO -> ())
    | Eventually (i, f) -> (match pol with
                            | SAT -> ()
                            | VIO -> ())
    | Historically (i, f) -> (match pol with
                              | SAT -> ()
                              | VIO -> ())
    | Always (i, f) -> (match pol with
                        | SAT -> ()
                        | VIO -> ())
    | Since (i, f1, f2) -> (match pol with
                            | SAT -> ()
                            | VIO -> ())
    | Until (i, f1, f2) -> (match pol with
                            | SAT -> ()
                            | VIO -> ())
  and since_sat i f1 f2 tp alphas_sat =
    if Interval.mem 0 i then
      ()
    else
      () in
  eval pol tp f

let exec mode measure f inc =
  let vars = Set.elements (Formula.fv f) in
  let out tstp_expls (ms: MState.t) =
    match mode with
    | Out.Plain.UNVERIFIED -> Out.Plain.expls tstp_expls None None None mode
    | Out.Plain.LATEX      -> Out.Plain.expls tstp_expls None None (Some(f)) mode
    | Out.Plain.LIGHT      -> Out.Plain.expls tstp_expls None None None mode
    | Out.Plain.VERIFIED ->
       let c = Checker_interface.check (Queue.to_list ms.tsdbs) f (List.map tstp_expls ~f:snd) in
       Out.Plain.expls tstp_expls (Some(c)) None None mode
    | Out.Plain.DEBUG ->
       let c = Checker_interface.check (Queue.to_list ms.tsdbs) f (List.map tstp_expls ~f:snd) in
       let paths = Checker_interface.false_paths (Queue.to_list ms.tsdbs) f (List.map tstp_expls ~f:snd) in
       Out.Plain.expls tstp_expls (Some(c)) (Some(paths)) None mode
    | Out.Plain.DEBUGVIS -> raise (Failure "function exec is undefined for the mode debugvis") in
  let rec step pb_opt ms =
    match Other_parser.Trace.parse_from_channel inc pb_opt with
    | Finished -> ()
    | Skipped (pb, msg) -> Stdio.printf "The parser skipped an event because %s" msg;
                           step (Some(pb)) ms
    | Processed pb -> let (tstp_expls, ms) = mstep mode vars pb.ts pb.db ms false in
                      out tstp_expls ms;
                      step (Some(pb)) ms in
  let mf = init f in
  let ms = MState.init mf in
  step None ms

let exec_vis (ms_opt: MState.t option) f log =
  let vars = Set.elements (Formula.fv f) in
  let step (ms: MState.t) db =
    (match Other_parser.Trace.parse_from_string db with
     | Finished -> None
     | Skipped (_, msg) -> Some (Some(msg), ([], []), ms)
     | Processed pb ->
        let last_ts = Hashtbl.fold ms.tpts ~init:0
                        ~f:(fun ~key:_ ~data:ts l_ts -> if ts > l_ts then ts else l_ts) in
        if pb.ts >= last_ts then
          (let (tstps_expls, ms') = mstep Out.Plain.UNVERIFIED vars pb.ts pb.db ms true in
           let tp_out' = List.fold tstps_expls ~init:ms'.tp_out ~f:(fun acc ((ts, tp), _) ->
                             Hashtbl.add_exn ms.tpts ~key:(acc + 1) ~data:ts; acc + 1) in
           let json_expls = Out.Json.expls ms.tpts f (List.map tstps_expls ~f:snd) in
           let json_db = Out.Json.db pb.ts ms.tp_cur pb.db f in
           Some (None, (json_expls, [json_db]), { ms' with tp_out = tp_out' }))
        else (Some (Some("trace is not monotonic"), ([], []), ms))) in
  let ms = match ms_opt with
    | None -> let mf = init f in
              MState.init mf
    | Some (ms') -> { ms' with tp_cur = ms'.tp_out + (Queue.length ms'.ts_waiting) + 1 } in
  let str_dbs = List.map (List.filter (String.split log ~on:'@') ~f:(fun s -> not (String.is_empty s)))
                  ~f:(fun s -> "@" ^ s) in
  let (err_msgs, (json_expls, json_dbs), ms) =
    List.fold str_dbs ~init:([], ([], []), ms)
      ~f:(fun (err_msgs, (json_es, json_dbs), m) str_db ->
        match step m str_db with
        | None -> (err_msgs, (json_es, json_dbs), m)
        | Some (None, (json_es', json_dbs'), m') ->
           (err_msgs, (json_es @ json_es', json_dbs @ json_dbs'), m')
        | Some (Some(err_msg), (json_es', json_dbs'), m') ->
           (err_msgs @ [err_msg], (json_es @ json_es', json_dbs @ json_dbs'), m')) in
  let json_errs = Etc.string_list_to_json err_msgs in
  let out_json = Out.Json.aggregate json_dbs json_expls json_errs in
  (ms, out_json)
