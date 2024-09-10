(*******************************************************************)
(*    This is part of WhyMyMon, and it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio
open Monitor_lib
open Monitor_lib.Etc

(* TODO: This module must be rewritten using the Command module from Core *)
module WhyMyMon = struct

  let mon_path_ref = ref ""
  let sig_path_ref = ref ""
  let formula_path_ref = ref ""

  let mon_ref = ref Argument.Monitor.MonPoly
  let pref_ref = ref Argument.Preference.Violation
  let mode_ref = ref Argument.Mode.Unverified
  let formula_ref = ref None
  let stream_ref = ref Stdio.In_channel.stdin
  let logstr_ref = ref ""

  let outc_ref = ref Stdio.Out_channel.stdout

  let nec_arg_count = ref 0

  let usage () =
    Format.eprintf
      "usage: ./whymymon.exe [-monitor <monitor>] [-path <file>] [-measure <measure>]
                           [-sig <file>] [-formula <file>] [-log <file>]
       arguments:
       \t -monitor
       \t\t monpoly            - (default)
       \t\t dejavu
       \t\t timelymon
       \t\t verimon
       \t -path
       \t\t default            - (default) path (folder third-party) for external monitors
       \t\t <file>             - chosen monitor's executable full path
       \t -pref
       \t\t vio                - explain violations (default)
       \t\t sat                - explain satisfactions
       \t -mode
       \t\t unverified         - (default)
       \t\t verified           - check output with formally verified checker
       \t -sig
       \t\t <file>             - signature
       \t -formula
       \t\t <file> or <string> - MFOTL formula
       \t -log
       \t\t <file>             - specify log file as stream (default: stdin)\n%!";
    exit 0

  let process_args =
    let rec process_args_rec = function
      | ("-monitor" :: m :: args) ->
         nec_arg_count := !nec_arg_count + 1;
         mon_ref := Argument.Monitor.of_string m;
         process_args_rec args
      | ("-path" :: p :: args) ->
         nec_arg_count := !nec_arg_count + 1;
         mon_path_ref := (if String.equal p "default" then
                            (Filename_unix.realpath (Argument.Monitor.exec_path !mon_ref))
                          else Filename_unix.realpath p);
         process_args_rec args
      | ("-pref" :: p :: args) ->
         pref_ref := Argument.Preference.of_string p;
         process_args_rec args
      | ("-mode" :: m :: args) ->
         mode_ref := Argument.Mode.of_string m;
         process_args_rec args
      | ("-sig" :: sf :: args) ->
         nec_arg_count := !nec_arg_count + 1;
         sig_path_ref := Filename_unix.realpath sf;
         Other_parser.Sig.parse_from_channel sf;
         process_args_rec args
      | ("-formula" :: f :: args) ->
         nec_arg_count := !nec_arg_count + 1;
         formula_path_ref := f;
         In_channel.with_file f ~f:(fun inc ->
             let lexbuf = Lexing.from_channel inc in
             formula_ref := try Some(Formula_parser.formula Formula_lexer.token lexbuf)
                            with Formula_parser.Error ->
                              Stdio.printf "%s\n" (Etc.lexbuf_error_msg lexbuf);
                              Stdlib.flush_all (); None);
         process_args_rec args
      | ("-log" :: f :: args) ->
         stream_ref := In_channel.create f;
         process_args_rec args
      | ("-logstr" :: logs :: args) ->
         logstr_ref := logs;
         process_args_rec args
      | [] -> if !nec_arg_count >= 3 then () else usage ()
      | _ -> usage () in
    process_args_rec

  let _ =
    try
      process_args (List.tl_exn (Array.to_list Sys.argv));
      match !mon_ref with
      | MonPoly -> let _ = Monitor.exec !mon_ref ~mon_path:!mon_path_ref ~sig_path:!sig_path_ref
                             !stream_ref (Option.value_exn !formula_ref) !pref_ref !mode_ref in ()
      | _ -> failwith "not yet"
    with End_of_file -> Out_channel.close !outc_ref; exit 0

end
