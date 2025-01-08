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
open Pred

module Fdeque = Core.Fdeque

module Part : sig

  type sub = (Dom.t, Dom.comparator_witness) Setc.t

  type 'a t

  val trivial: 'a -> 'a t
  val length: 'a t -> int
  val rev: 'a t -> 'a t
  val map: 'a t -> ('a -> 'b) -> 'b t
  val map2_list: 'a t -> (sub * 'a -> 'b) -> 'b list
  val fold_left: 'a t -> 'b -> ('b -> 'a -> 'b) -> 'b
  val fold_map_list: 'a t -> 'b -> ('b -> sub * 'a -> 'b * 'd) -> 'b * 'd list
  val filter: 'a t -> ('a -> bool) -> 'a t
  val exists: 'a t -> ('a -> bool) -> bool
  val unsomes: 'a option t -> 'a t
  val for_all: 'a t -> ('a -> bool) -> bool
  val values: 'a t -> 'a list
  val of_list: ((Dom.t, Dom.comparator_witness) Setc.t * 'a) list -> 'a t
  val tabulate: (Dom.t, Dom.comparator_witness) Set.t -> (Dom.t -> 'a) -> 'a -> 'a t

  val dedup: ('a -> 'a -> bool) -> 'a t -> 'a t
  val map_dedup: ('a -> 'a -> bool) -> 'd t -> ('d -> 'a) -> 'a t
  val map2_dedup: ('a -> 'a -> bool) -> 'a t -> (sub * 'a -> sub * 'a) -> 'a t
  val tabulate_dedup: ('a -> 'a -> bool) -> (Dom.t, Dom.comparator_witness) Set.t -> (Dom.t -> 'a) -> 'a -> 'a t

end

module Proof : sig

  type sp =
    | STT of int
    | SEqConst of int * string * Dom.t
    | SPred of int * string * Term.t list
    | SNeg of vp
    | SOrL of sp
    | SOrR of sp
    | SAnd of sp * sp
    | SImpL of vp
    | SImpR of sp
    | SIffSS of sp * sp
    | SIffVV of vp * vp
    | SExists of string * Dom.t * sp
    | SForall of string * (sp Part.t)
    | SPrev of sp
    | SNext of sp
    | SOnce of int * sp
    | SEventually of int * sp
    | SHistorically of int * int * sp Fdeque.t
    | SHistoricallyOut of int
    | SAlways of int * int * sp Fdeque.t
    | SSince of sp * sp Fdeque.t
    | SUntil of sp * sp Fdeque.t
  and vp =
    | VFF of int
    | VEqConst of int * string * Dom.t
    | VPred of int * string * Term.t list
    | VNeg of sp
    | VOr of vp * vp
    | VAndL of vp
    | VAndR of vp
    | VImp of sp * vp
    | VIffSV of sp * vp
    | VIffVS of vp * sp
    | VExists of string * (vp Part.t)
    | VForall of string * Dom.t * vp
    | VPrev of vp
    | VPrev0
    | VPrevOutL of int
    | VPrevOutR of int
    | VNext of vp
    | VNextOutL of int
    | VNextOutR of int
    | VOnceOut of int
    | VOnce of int * int * vp Fdeque.t
    | VEventually of int * int * vp Fdeque.t
    | VHistorically of int * vp
    | VAlways of int * vp
    | VSinceOut of int
    | VSince of int * vp * vp Fdeque.t
    | VSinceInf of int * int * vp Fdeque.t
    | VUntil of int * vp * vp Fdeque.t
    | VUntilInf of int * int * vp Fdeque.t

  type t = S of sp | V of vp

  val s_equal: sp -> sp -> bool
  val v_equal: vp -> vp -> bool
  val equal: t -> t -> bool
  val opt_s_equal: sp option -> sp option -> bool
  val opt_v_equal: vp option -> vp option -> bool
  val opt_equal: t option -> t option -> bool

  val unS: t -> sp
  val unV: t -> vp
  val opt_unS: t option -> sp
  val opt_unV: t option -> vp
  val isS: t -> bool
  val isV: t -> bool
  val opt_isS: t option -> bool
  val opt_isV: t option -> bool

  val s_append: t -> t -> t
  val v_append: t -> t -> t
  val s_drop: sp -> sp option
  val v_drop: vp -> vp option

  val s_at: sp -> int
  val v_at: vp -> int
  val p_at: t -> int

  val s_ertp: sp -> int
  val v_ertp: vp -> int
  val ertp: t -> int

  val s_lrtp: sp -> int
  val v_lrtp: vp -> int
  val lrtp: t -> int

  val s_to_string: string -> sp -> string
  val v_to_string: string -> vp -> string
  val to_string: string -> t -> string

  module Size : sig

    val minp_bool: t -> t -> bool
    val minp: t -> t -> t
    val minp_list: t list -> t option
    val minp_list_somes: t option list -> t option

  end

end

module Pdt : sig

  type 'a t = Leaf of 'a | Node of string * ('a t) Part.t

  val apply1: string list -> ('a -> 'b) -> 'a t -> 'b t
  val apply2: string list -> ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val apply3: string list -> ('a -> 'b -> 'c -> 'd) -> 'a t -> 'b t -> 'c t -> 'd t
  val split_prod: ('a * 'b) t -> 'a t * 'b t
  val split_list: 'a list t -> 'a t list
  val hide: string list -> ('a -> 'b) -> ('a Part.t -> 'b) -> 'a t -> 'b t
  val unleaf: 'a t -> 'a
  val is_leaf: 'a t -> bool
  val is_node: 'a t -> bool
  val to_string: (string -> 'a -> string) -> string -> 'a t -> string

  val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val reduce: ('a -> 'a -> bool) -> 'a t -> 'a t
  val apply1_reduce: ('a -> 'a -> bool) -> string list -> ('b -> 'a) -> 'b t -> 'a t
  val apply2_reduce: ('a -> 'a -> bool) -> string list -> ('b -> 'c -> 'a) -> 'b t -> 'c t -> 'a t
  val apply3_reduce: ('a -> 'a -> bool) -> string list -> ('b -> 'c -> 'd -> 'a) -> 'b t -> 'c t -> 'd t -> 'a t
  val split_prod_reduce: ('a -> 'a -> bool) -> ('a * 'a) t -> 'a t * 'a t
  val split_list_reduce: ('a -> 'a -> bool) -> 'a list t -> 'a t list
  val hide_reduce: ('a -> 'a -> bool) -> string list -> ('b -> 'a) -> ('b Part.t -> 'a) -> 'b t -> 'a t
  val somes: 'a t -> 'a option t
  val somes_pol: Polarity.t -> Proof.t t -> Proof.t option t
  val unsomes: 'a option t -> 'a t
  val uneither: ('a option, 'b) Either.t t -> 'a option t
  val prune_nones: 'a option t -> 'a t option

end

type t = Proof.t Pdt.t
type opt_t = Proof.t option Pdt.t

val equal: t -> t -> bool
val is_violated: t -> bool
val opt_is_violated: opt_t -> bool
val opt_is_satisfied: opt_t -> bool
val opt_is_none: opt_t -> bool
val at: t -> int
val sort_parts: t -> t
val ertp: t -> int
val lrtp: t -> int

val to_string: t -> string
val opt_to_string: opt_t -> string
val to_latex: Formula.t -> t -> string
val to_light_string: t -> string
