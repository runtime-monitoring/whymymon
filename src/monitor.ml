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

module Quantifier = struct

  type t = Existential | Universal

end

let do_neg (p_opt: Proof.t option) (pol: Polarity.t) =
  match p_opt, pol with
  | Some (S sp), VIO -> Some (Proof.V (VNeg sp))
  | Some (V vp), SAT -> Some (S (SNeg vp))
  | _ -> None

let do_and (p1_opt: Proof.t option) (p2_opt: Proof.t option) (pol: Polarity.t) : Proof.t option =
  Proof.Size.minp_list
    (match p1_opt, p2_opt, pol with
     | Some (S sp1), Some (S sp2), SAT -> [Proof.S (SAnd (sp1, sp2))]
     | None, Some (V vp2), VIO
       | Some (S _), Some (V vp2), VIO -> [V (VAndR (vp2))]
     | Some (V vp1), None, VIO
       | Some (V vp1), Some (S _), VIO -> [V (VAndL (vp1))]
     | Some (V vp1), Some (V vp2), VIO -> [(V (VAndL (vp1))); (V (VAndR (vp2)))]
     | _ -> [])

let do_or (p1_opt: Proof.t option) (p2_opt: Proof.t option) (pol: Polarity.t) : Proof.t option =
  Proof.Size.minp_list
    (match p1_opt, p2_opt, pol with
     | Some (S sp1), Some (S sp2), SAT -> [(S (SOrL (sp1))); (S (SOrR(sp2)))]
     | Some (S sp1), None, SAT
       | Some (S sp1), Some (V _), SAT -> [S (SOrL (sp1))]
     | None, Some (S sp2), SAT
       | Some (V _), Some (S sp2), SAT -> [S (SOrR (sp2))]
     | Some (V vp1), Some (V vp2), VIO -> [V (VOr (vp1, vp2))]
     | _ -> [])

let do_imp (p1_opt: Proof.t option) (p2_opt: Proof.t option) (pol: Polarity.t) : Proof.t option =
  Proof.Size.minp_list
    (match p1_opt, p2_opt, pol with
     | Some (S _), Some (S sp2), SAT -> [S (SImpR sp2)]
     | Some (S sp1), Some (V vp2), VIO -> [V (VImp (sp1, vp2))]
     | Some (V vp1), Some (S sp2), SAT -> [S (SImpL vp1); S (SImpR sp2)]
     | Some (V vp1), None, SAT
       | Some (V vp1), Some (V _), SAT -> [S (SImpL vp1)]
     | _ -> [])

let do_iff (p1_opt: Proof.t option) (p2_opt: Proof.t option) (pol: Polarity.t) : Proof.t option =
  match p1_opt, p2_opt, pol with
  | Some (S sp1), Some (S sp2), SAT -> Some (S (SIffSS (sp1, sp2)))
  | Some (S sp1), Some (V vp2), VIO -> Some (V (VIffSV (sp1, vp2)))
  | Some (V vp1), Some (S sp2), VIO -> Some (V (VIffVS (vp1, sp2)))
  | Some (V vp1), Some (V vp2), SAT -> Some (S (SIffVV (vp1, vp2)))

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
  else
    [Some (V (Proof.VExists (x, Part.map_dedup Proof.v_equal part Proof.opt_unV)))]

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

let maps_to_string maps =
  "> Map:" ^ String.concat (List.join (List.map maps ~f:(fun map ->
                                           List.map (Map.to_alist map) ~f:(fun (k, v) ->
                                               Printf.sprintf "%s -> %s\n" k (Dom.to_string v)))))

let do_prev i (p_opt: Proof.t option) ts ts' (pol: Polarity.t) =
  Proof.Size.minp_list
    (match p_opt, pol with
     | Some (S sp), SAT -> if Interval.mem (ts' - ts) i then
                             [Proof.S (SPrev sp)]
                           else []
     | Some (V vp), VIO -> if Interval.below (ts' - ts) i then
                             [Proof.V (VPrevOutL ((Proof.v_at vp)+1))]
                           else
                             (if (Interval.above (ts' - ts) i) then
                                [Proof.V (VPrevOutR ((Proof.v_at vp)+1))]
                              else [V (VPrev vp)])
     | _ -> [])

let do_next i (p_opt: Proof.t option) ts ts' (pol: Polarity.t) =
  Proof.Size.minp_list
    (match p_opt, pol with
     | Some (S sp), SAT -> if Interval.mem (ts' - ts) i then
                             [S (SNext sp)]
                           else []
     | Some (V vp), VIO -> if Interval.below (ts' - ts) i then
                             [V (VNextOutL ((Proof.v_at vp)-1))]
                           else
                             (if (Interval.above (ts' - ts) i) then
                                [V (VNextOutR ((Proof.v_at vp)-1))]
                              else [V (VNext vp)])
     | _ -> [])

let rec match_terms trms ds map =
  match trms, ds with
  | [], [] -> Some(map)
  | Term.Const c :: trms, d :: ds -> if Dom.equal c d then match_terms trms ds map else None
  | Var x :: trms, d :: ds -> (match match_terms trms ds map with
                               | None -> None
                               | Some(map') -> (match Map.find map' x with
                                                | None -> let map'' = Map.add_exn map' ~key:x ~data:d in
                                                          Some(map'')
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


module State = struct

  type t = { f: Formula.t
           ; pol: Polarity.t
           ; tp: timepoint
           ; expl: Expl.t }

end


let either_s_equal e e' = match e, e' with
  | First p, First p' -> Proof.opt_equal p p'
  | Second sps, Second sps' -> Etc.fdeque_for_all2 sps sps' ~f:Proof.s_equal
  | _ -> false

let either_v_equal e e' = match e, e' with
  | First p, First p' -> Proof.opt_equal p p'
  | Second vps, Second vps' -> Etc.fdeque_for_all2 vps vps' ~f:Proof.v_equal
  | _ -> false

(* Note that the polarity pol considered is the one on the bottom level *)
let rec stop_either vars vars_map expl (pol: Polarity.t) =
  (* traceln "STOP_EITHER |vars| = %d; pol = %s" (List.length vars) (Polarity.to_string pol); *)
  match vars, expl, pol with
  | [], Pdt.Leaf (Either.First (Some (Proof.S _))), SAT -> true
  | [], Leaf (First (Some (V _))), VIO -> true
  | x :: xs, Node (y, part), _ when String.equal x y ->
     let (kind, pol) = Map.find_exn vars_map x in
     (match kind, pol with
      | Quantifier.Existential, Polarity.SAT
        | Universal, VIO -> Part.exists part (fun expl -> stop_either xs vars_map expl pol)
      | Existential, VIO
        | Universal, SAT -> Part.for_all part (fun expl -> stop_either xs vars_map expl pol)
      | _ -> raise (Failure "stop: issue with variable ordering"))
  | _ -> false

let rec stop vars vars_map expl (pol: Polarity.t) = match vars, expl, pol with
  | [], Pdt.Leaf (Some (Proof.S _)), SAT -> true
  | [], Leaf (Some (V _)), VIO -> true
  | x :: xs, Node (y, part), _ when String.equal x y ->
     let (kind, pol) = Map.find_exn vars_map x in
     match kind, pol with
     | Quantifier.Existential, Polarity.SAT
       | Universal, VIO -> Part.exists part (fun expl -> stop xs vars_map expl pol)
     | Existential, VIO
       | Universal, SAT -> Part.for_all part (fun expl -> stop xs vars_map expl pol)
     | _ -> raise (Failure "stop: issue with variable ordering")

let explain prefix v pol tp f =
  (* traceln "assignment: %s" (Assignment.to_string v); *)
  (* traceln "tp = %d" tp; *)
  let rec eval vars (pol: Polarity.t) tp (f: Formula.t) vars_map = match f with
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
                                                        | None -> (* traceln "Var = %s" (Term.to_string trm); *)
                                                           trm
                                                        | Some d -> Const d)
                                                     else trm) in
       (* traceln "db = %s" (Db.to_string (snd (Array.get prefix tp))); *)
       let db = Set.filter (snd (Array.get prefix tp)) ~f:(fun evt -> String.equal r (fst(evt))) in
       let maps = Set.fold db ~init:[] ~f:(fun acc evt -> match_terms trms_subst (snd evt)
                                                            (Map.empty (module String)) :: acc) in
       (* traceln "|maps| = %d" (List.length maps); *)
       let maps' = List.map (List.filter maps ~f:(fun map_opt -> Option.is_some map_opt))
                     ~f:(fun map_opt -> Option.value_exn map_opt) in
       (* traceln "maps = %s" (maps_to_string maps'); *)
       let fvs = Set.of_list (module String) (Pred.Term.fv_list trms_subst) in
       (* traceln "|fvs| = %d" (Set.length fvs); *)
       (* traceln "|vars| = %d" (List.length vars); *)
       let vars = List.filter vars ~f:(fun x -> Set.mem fvs x) in
       (* traceln "|vars| = %d" (List.length vars); *)
       let expl = Pdt.somes_pol pol (pdt_of tp r trms vars maps') in
       (* traceln "PREDICATE %s expl = %s" (Polarity.to_string pol) (Expl.opt_to_string expl); *)
       (* match expl with *)
       (* | S  *)
       expl
    | Neg f ->
       let expl = eval vars (Polarity.invert pol) tp f vars_map in
       let expl = Pdt.apply1_reduce Proof.opt_equal vars
                    (fun p_opt -> do_neg p_opt pol) expl in
       (* traceln "NEG %s expl = %s" (Polarity.to_string pol) (Expl.to_string expl); *)
       expl
    | And (f1, f2) ->
       let expl1 = eval vars pol tp f1 vars_map in
       let expl2 = eval vars pol tp f2 vars_map in
       let expl = Pdt.apply2_reduce Proof.opt_equal vars
                    (fun p1_opt p2_opt -> (do_and p1_opt p2_opt pol)) expl1 expl2 in
       (* traceln "AND expl = %s" (Expl.to_string expl); *)
       expl
    | Or (f1, f2) ->
       let expl1 = eval vars pol tp f1 vars_map in
       let expl2 = eval vars pol tp f2 vars_map in
       Pdt.apply2_reduce Proof.opt_equal vars
         (fun p1_opt p2_opt -> (do_or p1_opt p2_opt pol)) expl1 expl2
    | Imp (f1, f2) ->
       let expl1 = eval vars pol tp f1 vars_map in
       let expl2 = eval vars pol tp f2 vars_map in
       let expl = Pdt.apply2_reduce Proof.opt_equal vars
                    (fun p1_opt p2_opt -> (do_imp p1_opt p2_opt pol)) expl1 expl2 in
       (* traceln "IMP expl = %s" (Expl.to_string expl); *)
       expl
    | Iff (f1, f2) ->
       let expl1 = eval vars pol tp f1 vars_map in
       let expl2 = eval vars pol tp f2 vars_map in
       Pdt.apply2_reduce Proof.opt_equal vars
         (fun p1_opt p2_opt -> (do_iff p1_opt p2_opt pol)) expl1 expl2
    | Exists (x, tc, f) ->
       let vars_map = Map.add_exn vars_map ~key:x ~data:(Quantifier.Existential, pol) in
       let expl = eval (vars @ [x]) pol tp f vars_map in
       let expl =
         Pdt.hide_reduce Proof.opt_equal (vars @ [x])
           (fun p_opt -> do_exists_leaf x tc p_opt)
           (fun part -> Proof.Size.minp_list_somes (do_exists_node x tc part)) expl in
       (* traceln "EXISTS expl = %s" (Expl.to_string expl); *)
       expl
    | Forall (x, tc, f) ->
       let vars_map = Map.add_exn vars_map ~key:x ~data:(Quantifier.Universal, pol) in
       let expl = eval (vars @ [x]) pol tp f vars_map in
       Pdt.hide_reduce Proof.opt_equal (vars @ [x])
         (fun p_opt -> do_forall_leaf x tc p_opt)
         (fun part -> Proof.Size.minp_list_somes (do_forall_node x tc part)) expl
    | Prev (i, f) ->
       if Int.equal tp 0 then
         (match pol with
          | SAT -> Pdt.Leaf None
          | VIO -> Pdt.Leaf (Some (V VPrev0)))
       else
         (let expl = eval vars pol tp f vars_map in
          let ts = fst (Array.get prefix tp) in
          let ts' = fst (Array.get prefix (tp-1)) in
          let expl = Pdt.apply1_reduce Proof.opt_equal vars
                       (fun p_opt -> do_prev i p_opt ts ts' pol) expl in
          expl)
    | Next (i, f) ->
       let expl = eval vars pol tp f vars_map in
       let ts = fst (Array.get prefix tp) in
       let ts' = fst (Array.get prefix (tp+1)) in
       let expl = Pdt.apply1_reduce Proof.opt_equal vars
                    (fun p_opt -> do_next i p_opt ts ts' pol) expl in
       expl
    | Once (i, f) -> (let ts = fst (Array.get prefix tp) in
                      let l = match Interval.right i with
                        | None -> 0
                        | Some b -> ts - b in
                      let r = ts - Interval.left i in
                      match pol with
                      | SAT -> let expl = once_sat tp (l,r) vars f tp (Pdt.Leaf None) vars_map in
                               (* traceln "ONCE_SAT expl = %s" (Expl.to_string expl); *)
                               expl
                      | VIO -> let expl = Pdt.uneither (once_vio tp (l,r) vars f tp
                                                          (Pdt.Leaf (Either.second Fdeque.empty)) vars_map) in
                               (* traceln "ONCE_VIO expl = %s" (Expl.to_string expl); *)
                               expl)
    | Eventually (i, f) -> (let ts = fst (Array.get prefix tp) in
                            let l = ts + Interval.left i in
                            let r = match Interval.right i with
                              | None -> raise (Failure "unbounded eventually")
                              | Some b -> ts + b in
                            match pol with
                            | SAT -> let expl = eventually_sat tp (l,r) vars f tp (Pdt.Leaf None) vars_map in
                                     (* traceln "EVENTUALLY_SAT expl = %s" (Expl.to_string expl); *)
                                     expl
                            | VIO -> let expl = Pdt.uneither (eventually_vio tp (l,r) vars f tp
                                                                (Pdt.Leaf (Either.second Fdeque.empty)) vars_map) in
                                     (* traceln "EVENTUALLY_VIO expl = %s" (Expl.to_string expl); *)
                                     expl)
    | Historically (i, f) -> (let ts = fst (Array.get prefix tp) in
                              let l = match Interval.right i with
                                | None -> 0
                                | Some b -> ts - b in
                              let r = ts - Interval.left i in
                              match pol with
                              | SAT -> let expl = Pdt.uneither (historically_sat tp (l,r) vars f tp
                                                                  (Pdt.Leaf (Either.second Fdeque.empty)) vars_map) in
                                       (* traceln "HISTORICALLY_SAT expl = %s" (Expl.to_string expl); *)
                                       expl
                              | VIO -> let expl = historically_vio tp (l,r) vars f tp (Pdt.Leaf None) vars_map in
                                       (* traceln "HISTORICALLY_VIO expl = %s" (Expl.to_string expl); *)
                                       expl)
    | Always (i, f) -> (let ts = fst (Array.get prefix tp) in
                        let l = ts + Interval.left i in
                        let r = match Interval.right i with
                          | None -> raise (Failure "unbounded always")
                          | Some b -> ts + b in
                        match pol with
                        | SAT -> let expl = Pdt.uneither (always_sat tp (l,r) vars f tp
                                                            (Pdt.Leaf (Either.second Fdeque.empty)) vars_map) in
                                 (* traceln "ALWAYS_SAT expl = %s" (Expl.to_string expl); *)
                                 expl
                        | VIO -> let expl = always_vio tp (l,r) vars f tp (Pdt.Leaf None) vars_map in
                                 (* traceln "ALWAYS_VIO expl = %s" (Expl.to_string expl); *)
                                 expl)
    | Since (i, f1, f2) -> (let ts = fst (Array.get prefix tp) in
                            let l = match Interval.right i with
                              | None -> 0
                              | Some b -> ts - b in
                            let r = ts - Interval.left i in
                            match pol with
                            | SAT -> let expl = Pdt.uneither
                                                  (since_sat (l,r) vars f1 f2 tp
                                                     (Pdt.Leaf (Either.second Fdeque.empty)) vars_map) in
                                     (* traceln "SINCE_SAT expl = %s" (Expl.to_string expl); *)
                                     expl
                            | VIO -> let expl =
                                       Pdt.uneither
                                         (since_vio tp (l,r) vars f1 f2 tp
                                            (Pdt.Leaf (Either.second Fdeque.empty)) vars_map) in
                                     (* traceln "SINCE_VIO (l=%d,r=%d) expl = %s" l r (Expl.to_string expl); *)
                                     expl)
    | Until (i, f1, f2) -> (let ts = fst (Array.get prefix tp) in
                            let l = ts + Interval.left i in
                            let r = match Interval.right i with
                              | None -> raise (Failure "unbounded until")
                              | Some b -> ts + b in
                            (* traceln "until (l,r) = (%d, %d)" l r; *)
                            match pol with
                            | SAT -> let expl = Pdt.uneither
                                                  (until_sat (l,r) vars f1 f2 tp
                                                     (Pdt.Leaf (Either.second Fdeque.empty)) vars_map) in
                                     (* traceln "SINCE_SAT expl = %s" (Expl.to_string expl); *)
                                     expl
                            | VIO -> let expl =
                                       Pdt.uneither
                                         (until_vio tp (l,r) vars f1 f2 tp
                                            (Pdt.Leaf (Either.second Fdeque.empty)) vars_map) in
                                     (* traceln "SINCE_VIO (l=%d,r=%d) expl = %s" l r (Expl.to_string expl); *)
                                     expl)

  (* Once *)
  and once_sat cur_tp (l,r) vars f tp mexpl vars_map =
    if tp < 0 || r < 0 then
      Pdt.apply1_reduce Proof.opt_equal vars (fun p_opt -> p_opt) mexpl
    else
      (let ts = fst (Array.get prefix tp) in
       if ts < l then
         Pdt.apply1_reduce Proof.opt_equal vars (fun p_opt -> p_opt) mexpl
       else
         (if ts <= r then
            (let expl = eval vars SAT tp f vars_map in
             let mexpl = Pdt.apply2_reduce Proof.opt_equal vars
                           (fun sp_opt p_opt ->
                             match p_opt with
                             | None -> (match sp_opt with
                                        | None -> None
                                        | Some (Proof.S sp) -> Some (Proof.S (SOnce (cur_tp, sp)))
                                        | _ -> raise (Invalid_argument "found V proof in S case"))
                             | Some p -> Some p) expl mexpl in
             if stop vars vars_map mexpl SAT then mexpl
             else once_sat cur_tp (l,r) vars f (tp-1) mexpl vars_map)
          else once_sat cur_tp (l,r) vars f (tp-1) mexpl vars_map))
  and once_vio cur_tp (l,r) vars f tp mexpl vars_map =
    if tp < 0 then
      Pdt.apply1_reduce either_v_equal vars
        (function First p -> First p
                | Second vps -> Either.first (Some (Proof.V (Proof.VOnce (cur_tp, tp+1, vps))))) mexpl
    else
      (if r < 0 then
         Pdt.apply1_reduce either_v_equal vars
           (function First p -> First p
                   | Second _ -> Either.first (Some (Proof.V (VOnceOut cur_tp)))) mexpl
       else
         (let ts = fst (Array.get prefix tp) in
          if ts < l then
            (Pdt.apply1_reduce either_v_equal vars
               (function First p -> First p
                       | Second vps -> Either.first (Some (Proof.V (Proof.VOnce (cur_tp, tp+1, vps))))) mexpl)
          else
            (if ts <= r then
               (let expl = eval vars VIO tp f vars_map in
                let mexpl = Pdt.apply2_reduce either_v_equal vars
                              (fun vp_opt p_vps ->
                                match p_vps with
                                | First p -> First p
                                | Second vps ->
                                   (match vp_opt with
                                    | None -> Either.first None
                                    | Some (Proof.V vp) -> Either.second (Fdeque.enqueue_front vps vp)
                                    | _ -> raise (Invalid_argument "found S proof in V case")))
                              expl mexpl in
                if stop_either vars vars_map mexpl VIO then mexpl
                else once_vio cur_tp (l,r) vars f (tp-1) mexpl vars_map)
             else once_vio cur_tp (l,r) vars f (tp-1) mexpl vars_map)))

  (* Eventually *)
  and eventually_sat cur_tp (l,r) vars f tp mexpl vars_map =
    let ts = fst (Array.get prefix tp) in
    if ts > r then
      Pdt.apply1_reduce Proof.opt_equal vars (fun p_opt -> p_opt) mexpl
    else
      (if ts >= l && ts <= r then
         (let expl = eval vars SAT tp f vars_map in
          let mexpl = Pdt.apply2_reduce Proof.opt_equal vars
                        (fun sp_opt p_opt ->
                          match p_opt with
                          | None -> (match sp_opt with
                                     | None -> None
                                     | Some (Proof.S sp) -> Some (Proof.S (SEventually (cur_tp, sp)))
                                     | _ -> raise (Invalid_argument "found V proof in S case"))
                          | Some p -> Some p) expl mexpl in
          if stop vars vars_map mexpl SAT then mexpl
          else eventually_sat cur_tp (l,r) vars f (tp+1) mexpl vars_map)
       else eventually_sat cur_tp (l,r) vars f (tp+1) mexpl vars_map)
  and eventually_vio cur_tp (l,r) vars f tp mexpl vars_map =
    let ts = fst (Array.get prefix tp) in
    if ts > r then
      Pdt.apply1_reduce either_v_equal vars
        (function First p -> First p
                | Second vps -> Either.first (Some (Proof.V (Proof.VEventually (cur_tp, tp-1, vps))))) mexpl
    else
      (if ts >= l && ts <= r then
         (let expl = eval vars VIO tp f vars_map in
          let mexpl = Pdt.apply2_reduce either_v_equal vars
                        (fun vp_opt p_vps ->
                          match p_vps with
                          | First p -> First p
                          | Second vps ->
                             (match vp_opt with
                              | None -> Either.first None
                              | Some (Proof.V vp) -> Either.second (Fdeque.enqueue_back vps vp)
                              | _ -> raise (Invalid_argument "found S proof in V case")))
                        expl mexpl in
          if stop_either vars vars_map mexpl VIO then mexpl
          else eventually_vio cur_tp (l,r) vars f (tp+1) mexpl vars_map)
       else eventually_vio cur_tp (l,r) vars f (tp+1) mexpl vars_map)

  (* Historically *)
  and historically_sat cur_tp (l,r) vars f tp mexpl vars_map =
    if tp < 0 then
      Pdt.apply1_reduce either_s_equal vars
        (function First p -> First p
                | Second sps -> Either.first (Some (Proof.S (Proof.SHistorically (cur_tp, tp+1, sps))))) mexpl
    else
      (if r < 0 then
         Pdt.apply1_reduce either_s_equal vars
           (function First p -> First p
                   | Second _ -> Either.first (Some (Proof.S (SHistoricallyOut cur_tp)))) mexpl
       else
         (let ts = fst (Array.get prefix tp) in
          if ts < l then
            (Pdt.apply1_reduce either_s_equal vars
               (function First p -> First p
                       | Second sps -> Either.first (Some (Proof.S (Proof.SHistorically (cur_tp, tp+1, sps))))) mexpl)
          else
            (if ts <= r then
               (let expl = eval vars SAT tp f vars_map in
                let mexpl = Pdt.apply2_reduce either_s_equal vars
                              (fun sp_opt p_sps ->
                                match p_sps with
                                | First p -> First p
                                | Second sps ->
                                   (match sp_opt with
                                    | None -> Either.first None
                                    | Some (Proof.S sp) -> Either.second (Fdeque.enqueue_front sps sp)
                                    | _ -> raise (Invalid_argument "found V proof in S case")))
                              expl mexpl in
                if stop_either vars vars_map mexpl SAT then mexpl
                else historically_sat cur_tp (l,r) vars f (tp-1) mexpl vars_map)
             else historically_sat cur_tp (l,r) vars f (tp-1) mexpl vars_map)))
  and historically_vio cur_tp (l,r) vars f tp mexpl vars_map =
    if tp < 0 || r < 0 then
      Pdt.apply1_reduce Proof.opt_equal vars (fun p_opt -> p_opt) mexpl
    else
      (let ts = fst (Array.get prefix tp) in
       if ts < l then
         Pdt.apply1_reduce Proof.opt_equal vars (fun p_opt -> p_opt) mexpl
       else
         (if ts <= r then
            (let expl = eval vars VIO tp f vars_map in
             let mexpl = Pdt.apply2_reduce Proof.opt_equal vars
                           (fun sp_opt p_opt ->
                             match p_opt with
                             | None -> (match sp_opt with
                                        | None -> None
                                        | Some (Proof.V vp) -> Some (Proof.V (VHistorically (cur_tp, vp)))
                                        | _ -> raise (Invalid_argument "found S proof in V case"))
                             | Some p -> Some p) expl mexpl in
             if stop vars vars_map mexpl VIO then mexpl
             else historically_vio cur_tp (l,r) vars f (tp-1) mexpl vars_map)
          else historically_vio cur_tp (l,r) vars f (tp-1) mexpl vars_map))

  (* Always *)
  and always_sat cur_tp (l,r) vars f tp mexpl vars_map =
    let ts = fst (Array.get prefix tp) in
    if ts > r then
      Pdt.apply1_reduce either_s_equal vars
        (function First p -> First p
                | Second sps -> Either.first (Some (Proof.S (Proof.SAlways (cur_tp, tp-1, sps))))) mexpl
    else
      (if ts >= l && ts <= r then
         (let expl = eval vars SAT tp f vars_map in
          let mexpl = Pdt.apply2_reduce either_s_equal vars
                        (fun sp_opt p_sps ->
                          match p_sps with
                          | First p -> First p
                          | Second sps ->
                             (match sp_opt with
                              | None -> Either.first None
                              | Some (Proof.S sp) -> Either.second (Fdeque.enqueue_back sps sp)
                              | _ -> raise (Invalid_argument "found V proof in S case")))
                        expl mexpl in
          if stop_either vars vars_map mexpl SAT then mexpl
          else always_sat cur_tp (l,r) vars f (tp+1) mexpl vars_map)
       else always_sat cur_tp (l,r) vars f (tp+1) mexpl vars_map)
  and always_vio cur_tp (l,r) vars f tp mexpl vars_map =
    let ts = fst (Array.get prefix tp) in
    if ts > r then
      Pdt.apply1_reduce Proof.opt_equal vars (fun p_opt -> p_opt) mexpl
    else
      (if ts >= l && ts <= r then
         (let expl = eval vars VIO tp f vars_map in
          let mexpl = Pdt.apply2_reduce Proof.opt_equal vars
                        (fun vp_opt p_opt ->
                          match p_opt with
                          | None -> (match vp_opt with
                                     | None -> None
                                     | Some (Proof.V vp) -> Some (Proof.V (VAlways (cur_tp, vp)))
                                     | _ -> raise (Invalid_argument "found S proof in V case"))
                          | Some p -> Some p) expl mexpl in
          if stop vars vars_map mexpl VIO then mexpl
          else always_vio cur_tp (l,r) vars f (tp+1) mexpl vars_map)
       else always_vio cur_tp (l,r) vars f (tp+1) mexpl vars_map)

  (* Since *)
  and since_sat (l,r) vars f1 f2 tp mexpl vars_map =
    if tp < 0 || r < 0 then
      Pdt.apply1_reduce either_s_equal vars
        (function First p -> First p
                | Second _ -> Either.first None) mexpl
    else
      (let ts = fst (Array.get prefix tp) in
       if ts < l then
         Pdt.apply1_reduce either_s_equal vars
           (function First p -> First p
                   | Second _ -> Either.first None) mexpl
       else
         (* ts is inside the interval *)
         (if ts <= r then
            (let expl1 = eval vars SAT tp f1 vars_map in
             let expl2 = eval vars SAT tp f2 vars_map in
             let mexpl = Pdt.apply3_reduce either_s_equal vars
                           (fun sp1_opt sp2_opt p_sp1s ->
                             match p_sp1s with
                             | First p -> First p
                             | Second sp1s ->
                                (match sp1_opt, sp2_opt with
                                 | None, None -> Either.first None
                                 | Some (Proof.S sp1), None ->
                                    (* Found alpha satisfaction within the interval *)
                                    Either.second (Fdeque.enqueue_front sp1s sp1)
                                 | _, Some (Proof.S sp2) ->
                                    (* Found beta satisfaction within the interval *)
                                    Either.first (Some (Proof.S (SSince (sp2, sp1s))))
                                 | _ -> raise (Invalid_argument "found V proof in S deque")))
                           expl1 expl2 mexpl in
             if stop_either vars vars_map mexpl SAT then mexpl
             else since_sat (l,r) vars f1 f2 (tp-1) mexpl vars_map)
          else
            (* ts is between cur_tp and (not including) r *)
            (let expl1 = eval vars SAT tp f1 vars_map in
             let mexpl = Pdt.apply2_reduce either_s_equal vars
                           (fun sp1_opt p_sp1s ->
                             match p_sp1s with
                             | First p -> First p
                             | Second sp1s ->
                                (match sp1_opt with
                                 | None -> Either.first None
                                 | Some (Proof.S sp1) ->
                                    (* Found alpha satisfaction *)
                                    Either.second (Fdeque.enqueue_front sp1s sp1)
                                 | _ -> raise (Invalid_argument "found V proof in S deque")))
                           expl1 mexpl in
             if stop_either vars vars_map mexpl SAT then mexpl
             else since_sat (l,r) vars f1 f2 (tp-1) mexpl vars_map)))
  and since_vio cur_tp (l,r) vars f1 f2 tp mexpl vars_map =
    if tp < 0 then
      Pdt.apply1_reduce either_v_equal vars
        (function First p -> First p
                | Second vp2s -> Either.first (Some (Proof.V (Proof.VSinceInf (cur_tp, tp+1, vp2s))))) mexpl
    else
      (if r < 0 then
         Pdt.apply1_reduce either_v_equal vars
           (function First p -> First p
                   | Second _ -> Either.first (Some (Proof.V (VSinceOut cur_tp)))) mexpl
       else
         (let ts = fst (Array.get prefix tp) in
          if ts < l then
            (Pdt.apply1_reduce either_v_equal vars
               (function First p -> First p
                       | Second vp2s -> Either.first (Some (Proof.V (Proof.VSinceInf (cur_tp, tp+1, vp2s))))) mexpl)
          else
            (if ts <= r then
               (let expl1 = eval vars VIO tp f1 vars_map in
                let expl2 = eval vars VIO tp f2 vars_map in
                let mexpl = Pdt.apply3_reduce either_v_equal vars
                              (fun vp1_opt vp2_opt p_vp2s ->
                                match p_vp2s with
                                | First p -> First p
                                | Second vp2s ->
                                   (match vp1_opt, vp2_opt with
                                    | None, Some (Proof.V vp2) ->
                                       (* Found only beta violation within the interval *)
                                       Either.second (Fdeque.enqueue_front vp2s vp2)
                                    | Some (Proof.V vp1), Some (Proof.V vp2) ->
                                       (* Found alpha and beta violation within the interval *)
                                       Either.first
                                         (Some (Proof.V (VSince (cur_tp, vp1, Fdeque.enqueue_front vp2s vp2))))
                                    | _ -> (* traceln "p1 = %s\n" (Proof.to_string "" p1); *)
                                       (* traceln "p2 = %s\n" (Proof.to_string "" p2); *)
                                       Either.first None)) expl1 expl2 mexpl in
                if stop_either vars vars_map mexpl VIO then mexpl
                else since_vio cur_tp (l,r) vars f1 f2 (tp-1) mexpl vars_map)
             else
               (let expl1 = eval vars VIO tp f1 vars_map in
                let mexpl = Pdt.apply2_reduce either_v_equal vars
                              (fun vp1_opt p_vp2s ->
                                match p_vp2s with
                                  First p -> First p
                                | Second vp2s ->
                                   (match vp1_opt with
                                    | None -> Second vp2s
                                    | Some (Proof.V vp1) ->
                                       Either.first (Some (Proof.V (Proof.VSince (cur_tp, vp1, Fdeque.empty))))))
                              expl1 mexpl in
                if stop_either vars vars_map mexpl VIO then mexpl
                else since_vio cur_tp (l,r) vars f1 f2 (tp-1) mexpl vars_map))))

  (* Until *)
  and until_sat (l,r) vars f1 f2 tp mexpl vars_map =
    let ts = fst (Array.get prefix tp) in
    if ts > r then
      Pdt.apply1_reduce either_s_equal vars
        (function First p -> First p
                | Second _ -> Either.first None) mexpl
    else
      (* ts is inside the interval *)
      (if ts >= l && ts <= r then
         (let expl1 = eval vars SAT tp f1 vars_map in
          let expl2 = eval vars SAT tp f2 vars_map in
          let mexpl = Pdt.apply3_reduce either_s_equal vars
                        (fun sp1_opt sp2_opt p_sp1s ->
                          match p_sp1s with
                          | First p -> First p
                          | Second sp1s ->
                             (match sp1_opt, sp2_opt with
                              | None, None -> Either.first None
                              | Some (Proof.S sp1), None ->
                                 (* Found alpha satisfaction within the interval *)
                                 Either.second (Fdeque.enqueue_back sp1s sp1)
                              | _, Some (Proof.S sp2) ->
                                 (* Found beta satisfaction within the interval *)
                                 Either.first (Some (Proof.S (SUntil (sp2, sp1s))))
                              | _ -> raise (Invalid_argument "found V proof in S deque")))
                        expl1 expl2 mexpl in
          if stop_either vars vars_map mexpl SAT then mexpl
          else until_sat (l,r) vars f1 f2 (tp+1) mexpl vars_map)
       else
         (* ts is between cur_tp (being evaluated) and (not including) l *)
         (let expl1 = eval vars SAT tp f1 vars_map in
          let mexpl = Pdt.apply2_reduce either_s_equal vars
                        (fun sp1_opt p_sp1s ->
                          match p_sp1s with
                          | First p -> First p
                          | Second sp1s ->
                             (match sp1_opt with
                              | None -> Either.first None
                              | Some (Proof.S sp1) ->
                                 (* Found alpha satisfaction *)
                                 Either.second (Fdeque.enqueue_back sp1s sp1)
                              | _ -> raise (Invalid_argument "found V proof in S deque")))
                        expl1 mexpl in
          if stop_either vars vars_map mexpl SAT then mexpl
          else until_sat (l,r) vars f1 f2 (tp+1) mexpl vars_map))
  and until_vio cur_tp (l,r) vars f1 f2 tp mexpl vars_map =
    let ts = fst (Array.get prefix tp) in
    (* traceln "tp = %d\n" tp; *)
    (* traceln "ts = %d\n" ts; *)
    if ts > r then
      Pdt.apply1_reduce either_v_equal vars
        (function First p -> First p
                | Second vp2s -> (* traceln "creating correct proof"; *)
                                 Either.first (Some (Proof.V (Proof.VUntilInf (cur_tp, tp-1, vp2s))))) mexpl
    else
      (if ts >= l && ts <= r then
         (let expl1 = eval vars VIO tp f1 vars_map in
          let expl2 = eval vars VIO tp f2 vars_map in
          let mexpl = Pdt.apply3_reduce either_v_equal vars
                        (fun vp1_opt vp2_opt p_vp2s ->
                          match p_vp2s with
                          | First p -> First p
                          | Second vp2s ->
                             (match vp1_opt, vp2_opt with
                              | None, None -> (* traceln "mexpl 1"; *)
                                              Either.first None
                              | None, Some p -> (* traceln "mexpl 2"; *)
                                                (* traceln "proof: %s" (Proof.to_string "" p); *)
                                                Either.second (Fdeque.enqueue_back vp2s (Proof.unV p))
                              | Some p, None -> (* traceln "mexpl 3"; *)
                                                (* traceln "proof: %s" (Proof.to_string "" p); *)
                                                Either.first None
                              | Some p1, Some p2 -> (* traceln "mexpl 4"; *)
                                                    (* traceln "proof1: %s" (Proof.to_string "" p1); *)
                                                    (* traceln "proof2: %s" (Proof.to_string "" p2); *)
                                                    Either.first
                                                      (Some (Proof.V (VUntil (cur_tp, (Proof.unV p1),
                                                                              Fdeque.enqueue_back vp2s (Proof.unV p2)))))



                              (* | None, Some (Proof.V vp2) -> *)
                              (*    (\* Found only beta violation within the interval *\) *)
                              (*    traceln "mexpl 1"; *)
                              (*    Either.second (Fdeque.enqueue_back vp2s vp2) *)
                              (* | Some (Proof.V vp1), Some (Proof.V vp2) -> *)
                              (*    (\* Found alpha and beta violation within the interval *\) *)
                              (*    traceln "mexpl 2"; *)
                              (*    Either.first *)
                              (*      (Some (Proof.V (VUntil (cur_tp, vp1, Fdeque.enqueue_back vp2s vp2)))) *)
                              (* | Some _, None -> traceln "mexpl 3"; Either.first None *)
                              (* | None, None -> (\* traceln "p1 = %s\n" (Proof.to_string "" p1); *\) *)
                              (*    (\* traceln "p2 = %s\n" (Proof.to_string "" p2); *\) *)
                              (*    traceln "mexpl 4"; *)
                              (*    Either.first None *))) expl1 expl2 mexpl in
          if stop_either vars vars_map mexpl VIO then mexpl
          else until_vio cur_tp (l,r) vars f1 f2 (tp+1) mexpl vars_map)
       else
         (let expl1 = eval vars VIO tp f1 vars_map in
          let mexpl = Pdt.apply2_reduce either_v_equal vars
                        (fun vp1_opt p_vp2s ->
                          match p_vp2s with
                            First p -> First p
                          | Second vp2s ->
                             (match vp1_opt with
                              | None -> Second vp2s
                              | Some (Proof.V vp1) ->
                                 Either.first (Some (Proof.V (Proof.VUntil (cur_tp, vp1, Fdeque.empty))))))
                        expl1 mexpl in
          if stop_either vars vars_map mexpl VIO then mexpl
          else until_vio cur_tp (l,r) vars f1 f2 (tp+1) mexpl vars_map)) in
  eval [] pol tp f (Map.empty (module String))

(* Spawn thread to execute WhyMyMon somewhere in this function *)
let read (mon: Argument.Monitor.t) r_buf r_sink prefix f pol mode vars =
  while true do
    let line = Eio.Buf_read.line r_buf in
    traceln "Read emonitor line: %s" line;
    if String.equal line "Stop" then raise Exit;
    if Emonitor.is_verdict mon line then
      (let (tp, ts, assignments) = Emonitor.to_tpts_assignments mon vars line in
       traceln "%s" (Etc.string_list_to_string ~sep:"\n" (List.map assignments ~f:Assignment.to_string));
       List.iter assignments ~f:(fun v ->
           (* Stdio.printf "expl = %s\n" (Expl.opt_to_string (explain !prefix v pol tp f)); *)
           let expl = Pdt.unsomes (explain !prefix v pol tp f) in
           match mode with
           | Argument.Mode.Unverified -> Out.Plain.print (Explanation ((ts, tp), expl))
           | Verified ->
              let (b, _, _) = Checker_interface.check (Array.to_list !prefix) v f (Pdt.unleaf expl) in
              Out.Plain.print (ExplanationCheck ((ts, tp), expl, b))
           | LaTeX -> Out.Plain.print (ExplanationLatex ((ts, tp), expl, f))
           | Debug ->
              let (b, c_e, c_trace) = Checker_interface.check (Array.to_list !prefix) v f (Pdt.unleaf expl) in
              Out.Plain.print (ExplanationCheckDebug ((ts, tp), v, expl, b, c_e, c_trace))
           | DebugVis -> ()))
    else
      (* (get_pos output to keep track of progress *)
      (traceln "Read current progress";
       let tp = Emonitor.parse_prog_tp mon line in
       if Int.equal (Array.length !prefix - 1) tp then (Eio.Flow.copy_string "Stop\n" r_sink));
    Fiber.yield ()
  done

let write (mon: Argument.Monitor.t) w_sink stream prefix =
  let rec step pb_opt =
    match Other_parser.Trace.parse_from_channel stream pb_opt with
    | Finished -> traceln "Reached the end of event stream";
                  Eio.Flow.copy_string "> get_pos <\n" w_sink;
                  Fiber.yield ()
    | Skipped (pb, msg) -> traceln "Skipped time-point due to: %S" msg;
                           Fiber.yield ();
                           step (Some(pb))
    | Processed pb -> traceln "Processed event with time-stamp %d. Sending it to sink." pb.ts;
                      Eio.Flow.copy_string (Emonitor.write_line mon (pb.ts, pb.db)) w_sink;
                      Eio.Flow.copy_string "> get_pos <\n" w_sink;
                      prefix := Array.append !prefix [|(pb.ts, pb.db)|];
                      Fiber.yield ();
                      step (Some(pb)) in
  step None

(* sig_path is only passed as a parameter when either MonPoly or VeriMon is the external monitor *)
let exec mon ~mon_path ?sig_path ~formula_file stream f pref mode extra_args =
  let pol = Polarity.of_pref pref in
  let vars = Set.elements (Formula.fv f) in
  let ( / ) = Eio.Path.( / ) in
  Eio_main.run @@ fun env ->
    (* Formula conversion *)
    let f_path = Eio.Stdenv.cwd env / ("tmp/" ^ formula_file ^ ".mfotl") in
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
      let r_buf = Eio.Buf_read.of_flow r_source ~initial_size:100 ~max_size:1_000_000 in
      (* accumulated prefix ref *)
      let prefix = ref [||]  in
      try
        Fiber.all
          [
            (* Spawn thread with external monitor process *)
            (fun () -> let f_realpath = Filename_unix.realpath (Eio.Path.native_exn f_path) in
                       let args = Emonitor.args mon ~mon_path ?sig_path ~f_path:f_realpath in
                       traceln "Running process with: %s" (Etc.string_list_to_string ~sep:" " args);
                       Eio.Process.run ~stdin:w_source ~stdout:r_sink ~stderr:r_sink
                         proc_mgr (args @ extra_args));
            (* External monitor I/O management *)
            (fun () -> traceln "Writing lines to emonitor's stdin...";
                       write mon w_sink stream prefix);
            (fun () -> traceln "Reading lines from emonitor's stdout...";
                       read mon r_buf r_sink prefix f pol mode vars);
          ];
      with Exit -> Stdio.printf "Reached the end of the log file.\n");
