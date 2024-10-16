(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio
open Etc
open Checker_interface

module Plain = struct

  type t =
    | Explanation of (timestamp * timepoint) * Expl.t
    | ExplanationCheck of (timestamp * timepoint) * Expl.t * bool
    | ExplanationLatex of (timestamp * timepoint) * Expl.t * Formula.t
    | ExplanationLight of (timestamp * timepoint) * Expl.t
    | ExplanationCheckDebug of (timestamp * timepoint) * Expl.t * bool * Checker_proof.t * Checker_trace.t

  let print = function
    | Explanation ((ts, tp), e) ->
       Stdio.printf "%d:%d\nExplanation: \n\n%s\n\n" ts tp (Expl.to_string e)
    | ExplanationCheck ((ts, tp), e, b) ->
       Stdio.printf "%d:%d\nExplanation: \n\n%s\n" ts tp (Expl.to_string e);
       Stdio.printf "\nChecker output: %B\n\n" b;
    | ExplanationLatex ((ts, tp), e, f) ->
       Stdio.printf "%d:%d\nExplanation: \n\n%s\n\n" ts tp (Expl.to_latex f e)
    | ExplanationLight ((ts, tp), e) ->
       Stdio.printf "%d:%d\nExplanation: \n\n%s\n\n" ts tp (Expl.to_light_string e)
    | ExplanationCheckDebug ((ts, tp), e, b, c_e, c_t) ->
       Stdio.printf "%d:%d\nExplanation: \n\n%s\n" ts tp (Expl.to_string e);
       Stdio.printf "\nChecker output: %B\n\n" b;
       Stdio.printf "\n[debug] Checker explanation:\n%s\n\n" (Checker_interface.Checker_proof.to_string "" c_e);
       Stdio.printf "\n[debug] Checker trace:\n%s" (Checker_interface.Checker_trace.to_string c_t);

end

(* module Json = struct *)

(*   let error err = *)
(*     Printf.sprintf "ERROR: %s" (Error.to_string_hum err) *)

(*   let table_columns f = *)
(*     let sig_preds_columns = List.rev (Set.fold (Formula.pred_names f) ~init:[] ~f:(fun acc r -> *)
(*                                           let r_props = Hashtbl.find_exn Pred.Sig.table r in *)
(*                                           let var_names = fst (List.unzip r_props.ntconsts) in *)
(*                                           (Printf.sprintf "%s(%s)" r *)
(*                                              (Etc.string_list_to_string ~sep:", " var_names)) :: acc)) in *)
(*     let subfs_columns = List.map (Formula.subfs_dfs f) ~f:Formula.op_to_string in *)
(*     let subfs_scope = List.map (Formula.subfs_scope f 0) ~f:(fun (i, (js, ks)) -> *)
(*                           Printf.sprintf "{\"col\": %d, \"leftCols\": %s, \"rightCols\": %s}" *)
(*                             i (Etc.int_list_to_json js) (Etc.int_list_to_json ks)) in *)
(*     let subfs = List.map (Formula.subfs_dfs f) ~f:(Formula.to_string true) in *)
(*     Printf.sprintf "{\n  \"predsColumns\": %s,\n *)
(*                     \"subfsColumns\": %s,\n *)
(*                     \"subfsScopes\": [%s],\n *)
(*                     \"subformulas\": %s }\n" *)
(*       (Etc.string_list_to_json sig_preds_columns) (Etc.string_list_to_json subfs_columns) *)
(*       (Etc.string_list_to_string ~sep:", " subfs_scope) (Etc.string_list_to_json subfs) *)

(*   let db ts tp db f = *)
(*     Printf.sprintf "%s{\n" (String.make 4 ' ') ^ *)
(*       Printf.sprintf "%s\"ts\": %d,\n" (String.make 8 ' ') ts ^ *)
(*         Printf.sprintf "%s\"tp\": %d,\n" (String.make 8 ' ') tp ^ *)
(*           Printf.sprintf "%s\n" (Vis.Dbs.to_json tp db f) ^ *)
(*             Printf.sprintf "%s}" (String.make 4 ' ') *)

(*   let expls tpts f es = *)
(*     List.map es ~f:(fun e -> *)
(*         let tp = (Expl.at e) in *)
(*         let ts = Hashtbl.find_exn tpts tp in *)
(*         Printf.sprintf "%s{\n" (String.make 4 ' ') ^ *)
(*           Printf.sprintf "%s\"ts\": %d,\n" (String.make 8 ' ') ts ^ *)
(*             Printf.sprintf "%s\"tp\": %d,\n" (String.make 8 ' ') tp ^ *)
(*               Printf.sprintf "%s\"expl\": {\n" (String.make 8 ' ') ^ *)
(*                 Printf.sprintf "%s\n" (Vis.Expl.to_json f (Expl.sort_parts e)) ^ *)
(*                   Printf.sprintf "}%s}" (String.make 4 ' ')) *)

(*   let aggregate dbs expls errors = *)
(*     Printf.sprintf "{\n" ^ *)
(*       Printf.sprintf "%s\"dbs_objs\": [\n" (String.make 4 ' ') ^ *)
(*         String.concat ~sep:",\n" dbs ^ *)
(*           Printf.sprintf "],\n" ^ *)
(*             Printf.sprintf "%s\"expls_objs\": [\n" (String.make 4 ' ') ^ *)
(*               String.concat ~sep:",\n" expls ^ *)
(*                 Printf.sprintf "],\n" ^ *)
(*                   Printf.sprintf "%s\"errors\": %s\n" (String.make 4 ' ') errors ^ *)
(*                     Printf.sprintf "}" *)

(* end *)
