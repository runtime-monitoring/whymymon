(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio

module Term = struct

  module T = struct

    type t = Var of string | Const of Dom.t [@@deriving compare, sexp_of, hash]

    let unvar = function
      | Var x -> x
      | Const _ -> raise (Invalid_argument "unvar is undefined for Consts")

    let unconst = function
      | Var _ -> raise (Invalid_argument "unconst is undefined for Vars")
      | Const c -> c

    let is_var = function
      | Var _ -> true
      | Const _ -> false

    let is_const = function
      | Var _ -> false
      | Const _ -> true

    let rec fv_list = function
      | [] -> []
      | Const c :: trms -> fv_list trms
      | Var x :: trms -> x :: fv_list trms

    let equal t t' = match t, t' with
      | Var x, Var x' -> String.equal x x'
      | Const d, Const d' -> Dom.equal d d'
      | _ -> false

    let to_string = function
      | Var x -> Printf.sprintf "Var %s" x
      | Const d -> Printf.sprintf "Const %s" (Dom.to_string d)

    let value_to_string = function
      | Var x -> Printf.sprintf "%s" x
      | Const d -> Printf.sprintf "%s" (Dom.to_string d)

    let rec list_to_string trms =
      match trms with
      | [] -> ""
      | (Var x) :: trms -> if List.is_empty trms then x
                           else Printf.sprintf "%s, %s" x (list_to_string trms)
      | (Const d) :: trms -> if List.is_empty trms then (Dom.to_q_string d)
                             else Printf.sprintf "%s, %s" (Dom.to_q_string d) (list_to_string trms)

    let rec list_to_json_string trms =
      match trms with
      | [] -> ""
      | (Var x) :: trms -> if List.is_empty trms then x
                           else Printf.sprintf "%s, %s" x (list_to_json_string trms)
      | (Const d) :: trms -> if List.is_empty trms then "<" ^ (Dom.to_string d) ^ ">"
                             else Printf.sprintf "<%s>, %s" (Dom.to_string d) (list_to_json_string trms)

  end

  include T
  include Comparator.Make(T)

end

module Sig = struct

  type props = { arity: int; ntconsts: (string * Dom.tt) list } [@@deriving compare, sexp_of, hash]

  type t = string * props [@@deriving compare, sexp_of, hash]

  let table: (string, props) Hashtbl.t = Hashtbl.create (module String)

  let add p_name ntconsts = Hashtbl.add_exn table ~key:p_name ~data:{ arity = List.length ntconsts; ntconsts }

  let vars name = List.map (Hashtbl.find_exn table name).ntconsts ~f:fst

  let var_tt x = List.find_map_exn (Hashtbl.to_alist table) ~f:(fun (_, props) ->
                     List.find_map props.ntconsts ~f:(fun (y, tt) ->
                         if String.equal x y then Some(tt) else None))

  let print_table () =
    Hashtbl.iteri table ~f:(fun ~key:n ~data:ps ->
        Stdio.printf "%s(%s)\n" n
          (String.drop_prefix (List.fold ps.ntconsts ~init:"" ~f:(fun acc (var, tt) ->
                                   acc ^ "," ^ var ^ ":" ^ (Dom.tt_to_string tt))) 1))

end

let check_terms p_name trms =
  let sig_pred = Hashtbl.find_exn Sig.table p_name in
  if List.length trms = sig_pred.arity then
    if (List.for_all2_exn trms sig_pred.ntconsts
          ~f:(fun t ntc -> match t with
                           | Term.Var x -> true
                           | Const c -> Dom.tt_equal (Dom.tt_of_domain c) (snd ntc))) then trms
    else raise (Invalid_argument (Printf.sprintf "type of terms of %s do not match the signature" p_name))
  else raise (Invalid_argument (Printf.sprintf "arity of %s is %d" p_name sig_pred.arity))
