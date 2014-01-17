(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* WARNING: DO NOT EDIT THE .ML FILE --- CHANGES WILL BE OVERWRITTEN 

   Do not edit the .ml file but rather the .ml.in file, the .ml file
   is generated from the .ml.in file after each run of the configure
   script.

*)

open Lib

(* ********************************************************************** *)
(* Types and defaults for flags                                            *)
(* ********************************************************************** *)

(* TODO: write camlp4 code for this 
  
   type <X> = <X1> | <X2> arg <O> default <X2> action <F> doc <D>
      
   becomes 
   
   type <X> = <X1> | <X2>

   let <X>_of_string = function
     | "<X1>" -> <X1>
     | "<X2>" -> <X2>
     | _ raise (Arg.bad "Bad value for -<O>")

   let string_of_<X> = function 
     | <X1> -> "<X1>"
     | <X2> -> "<X2>"

   let <X>_values = "<X1>, <X2>"

   let <X>_default = <X2>

   let <O>_spec = 
     ("-<O>", 
      String <F>, 
      Format.sprintf <D> <X>_values <X>_default)

*)
      

(*   type <X> = <X1> | <X2> arg <O> default <X2> action <F> doc <D> *)

(*   type smtsolver = Z3_SMTLIB | CVC4_SMTLIB arg smtsolver default CVC4_SMTLIB action smtsolver_action doc " choose SMT solver (available: %s, default: %s" *)
  
(* ********** *) 

let timeout_wall_default = 0. 

(* ********** *) 

let timeout_virtual_default = 0. 

(* ********** *) 

type smtsolver = [ `Z3_SMTLIB | `Z3_API | `CVC4_SMTLIB | `CVC4_API | `Yices ]
    
let smtsolver_of_string = function
  | "Z3" -> `Z3_SMTLIB
  | "Z3_SMTLIB" -> `Z3_SMTLIB
  | "Z3_API" -> `Z3_API
  | "CVC4" -> `CVC4_SMTLIB
  | "CVC4_SMTLIB" -> `CVC4_SMTLIB
  | "CVC4_API" -> `CVC4_API
  | "Yices" -> `Yices
  | _ -> raise (Arg.Bad "Bad value for --smtsolver")

let string_of_smtsolver = function 
  | `Z3_SMTLIB -> "Z3_SMTLIB"
  | `Z3_API -> "Z3_API"
  | `CVC4_SMTLIB -> "CVC4_SMTLIB"
  | `CVC4_API -> "CVC4_API"
  | `Yices -> "Yices"

let smtsolver_values = "Z3, CVC4"

let smtsolver_default = `Z3_SMTLIB

(* ********** *) 

type z3_bin = string 

let z3_bin_of_string s = s

let string_of_z3_bin s = s 

let z3_bin_default = "/usr/bin/z3"

(* ********** *) 

type cvc4_bin = string 

let cvc4_bin_of_string s = s

let string_of_cvc4_bin s = s 

let cvc4_bin_default = ""

(* ********** *) 

(* type kind_module = [ `PDR | `BMC | `IND | `INVGEN ] *)

type enable = kind_module list 

let kind_module_of_string = function
  | "PDR" -> `PDR
  | "BMC" -> `BMC
  | "IND" -> `IND
  | "INVGEN" -> `INVGEN
  | "interpreter" -> `Interpreter
  | _ -> raise (Arg.Bad "Bad value for --enable")

let string_of_kind_module = function
  | `PDR -> "PDR"
  | `BMC -> "BMC"
  | `IND -> "IND"
  | `INVGEN -> "INVGEN"
  | `Interpreter -> "interpreter"

let rec string_of_enable' accum = function 
  | [] -> accum
  | m :: tl -> 
    string_of_enable'
      ((string_of_kind_module m) ^ 
          (if not (tl = []) then ", " else ""))
      tl

let string_of_enable = string_of_enable' ""

let enable_values = "PDR, BMC, IND, INVGEN"

let enable_default_init = []

let enable_default_after = [`PDR; `BMC; `IND]

(* ********** *) 

type pdr_subs_timeout = int
    
let string_of_pdr_subs_timeout = string_of_int

let pdr_subs_timeout_default = 500

(* ********** *) 

type pdr_check_inductive = bool
    
let string_of_pdr_check_inductive = string_of_bool

let pdr_check_inductive_default = false

(* ********** *) 

type pdr_fwd_prop_check_multi = bool
    
let string_of_pdr_fwd_prop_check_multi = string_of_bool

let pdr_fwd_prop_check_multi_default = true

(* ********** *) 

type pdr_dump_inductive_assertions = bool
    
let string_of_pdr_dump_inductive_assertions = string_of_bool

let pdr_dump_inductive_assertions_default = false

(* ********** *) 

type pdr_inductive_assertions_file = string option
    
let pdr_inductive_assertions_file_default = None

(* ********** *) 

type pdr_minimize_cex = bool
    
let string_of_pdr_minimize_cex = string_of_bool

let pdr_minimize_cex_default = false

(* ********** *) 

type pdr_tighten_to_unsat_core = bool
    
let string_of_pdr_tighten_to_unsat_core = string_of_bool

let pdr_tighten_to_unsat_core_default = false

(* ********** *) 

type pdr_block_in_future = bool
    
let string_of_pdr_block_in_future = string_of_bool

let pdr_block_in_future_default = false

(* ********** *) 

type pdr_prop_in_last_frame = bool
    
let string_of_pdr_prop_in_last_frame = string_of_bool

let pdr_prop_in_last_frame_default = false

(* ********** *) 

type pdr_qe = [ `Z3 | `Cooper ]
    
let pdr_qe_of_string = function
  | "Z3" -> `Z3
  | "cooper" -> `Cooper
  | _ -> raise (Arg.Bad "Bad value for -pdr_qe")

let string_of_pdr_qe = function 
  | `Z3 -> "Z3"
  | `Cooper -> "cooper"

let pdr_qe_values = "Z3, cooper"

let pdr_qe_default = `Z3

(* ********** *) 
 
type cooper_order_var_by_elim = bool 
     
let cooper_order_var_by_elim_values = "true, false"
 
let cooper_order_var_by_elim_default = false
 
(* ********** *) 
 
type cooper_general_lbound = bool
     
let cooper_general_lbound_values = "true, false"
 
let cooper_general_lbound_default = false

(* ********** *) 

let debug_default = []

(* ********** *) 

let debug_log_default = None

(* ********** *) 

let log_level_default = Event.L_warn

(* ********** *) 

let log_format_xml_default = false

(* ********** *) 

(* All flags *)
type flags = 
    { mutable timeout_wall : float;
      mutable timeout_virtual : float;
      mutable smtsolver : smtsolver;
      mutable z3_bin : z3_bin;
      mutable cvc4_bin : cvc4_bin;
      mutable enable : enable;
      mutable pdr_qe : pdr_qe;
      mutable pdr_subs_timeout : pdr_subs_timeout;
      mutable pdr_check_inductive : pdr_check_inductive;
      mutable pdr_fwd_prop_check_multi : pdr_fwd_prop_check_multi;
      mutable pdr_dump_inductive_assertions : pdr_dump_inductive_assertions;
      mutable pdr_inductive_assertions_file : pdr_inductive_assertions_file;
      mutable pdr_minimize_cex : pdr_minimize_cex;
      mutable pdr_tighten_to_unsat_core : pdr_tighten_to_unsat_core;
      mutable pdr_block_in_future : pdr_block_in_future;
      mutable pdr_prop_in_last_frame : pdr_prop_in_last_frame;
      mutable cooper_order_var_by_elim : cooper_order_var_by_elim;
      mutable cooper_general_lbound : cooper_general_lbound;
      mutable debug : string list;
      mutable debug_log : string option;
      mutable log_level : Event.log_level;
      mutable log_format_xml : bool;
      mutable input_file : string option }
    
(* Defaults for all flags *)
let flags = 
  { timeout_wall = timeout_wall_default;
    timeout_virtual = timeout_virtual_default;
    smtsolver = smtsolver_default;
    z3_bin = z3_bin_default;
    cvc4_bin = cvc4_bin_default;
    enable = enable_default_init;
    pdr_qe = pdr_qe_default;
    pdr_subs_timeout = pdr_subs_timeout_default;
    pdr_check_inductive = pdr_check_inductive_default;
    pdr_fwd_prop_check_multi = pdr_fwd_prop_check_multi_default;
    pdr_dump_inductive_assertions = pdr_dump_inductive_assertions_default;
    pdr_inductive_assertions_file = pdr_inductive_assertions_file_default;
    pdr_minimize_cex = pdr_minimize_cex_default;
    pdr_tighten_to_unsat_core = pdr_tighten_to_unsat_core_default;
    pdr_block_in_future = pdr_block_in_future_default;
    pdr_prop_in_last_frame = pdr_prop_in_last_frame_default;
    cooper_order_var_by_elim = cooper_order_var_by_elim_default;
    cooper_general_lbound = cooper_general_lbound_default;
    debug = debug_default;
    debug_log = debug_log_default;
    log_level = log_level_default;
    log_format_xml = log_format_xml_default;
    input_file = None } 

(* ********** *) 

let timeout_wall_action o = flags.timeout_wall <- o  

let timeout_wall_spec = 
  ("-timeout_wall", 
   Arg.Float timeout_wall_action, 
   Format.sprintf "wallclock timeout (default: %1.f)" timeout_wall_default)

(* ********** *) 

let timeout_virtual_action o = flags.timeout_virtual <- o  

let timeout_virtual_spec = 
  ("-timeout_virtual", 
   Arg.Float timeout_virtual_action, 
   Format.sprintf "CPU timeout (default: %1.f)" timeout_virtual_default)

(* ********** *) 

let smtsolver_action o = flags.smtsolver <- (smtsolver_of_string o)
  
let smtsolver_spec = 
  ("--smtsolver", 
   Arg.String smtsolver_action, 
   Format.sprintf "choose SMT solver (available: %s, default: %s)" smtsolver_values (string_of_smtsolver smtsolver_default))

(* ********** *) 

let z3_bin_action o = flags.z3_bin <- (z3_bin_of_string o)
  
let z3_bin_spec = 
  ("--z3_bin", 
   Arg.String z3_bin_action, 
   Format.sprintf "executable of Z3 solver (default: %s)" (string_of_z3_bin z3_bin_default))

(* ********** *) 

let cvc4_bin_action o = flags.cvc4_bin <- (cvc4_bin_of_string o)
  
let cvc4_bin_spec = 
  ("--cvc4_bin", 
   Arg.String cvc4_bin_action, 
   Format.sprintf "executable of CVC4 solver (default: %s)" (string_of_cvc4_bin cvc4_bin_default))

(* ********** *) 

let enable_action o = flags.enable <- (kind_module_of_string o) :: flags.enable
  
let enable_spec = 
  ("--enable", 
   Arg.String enable_action, 
   Format.sprintf "enable Kind module (available: %s, default: %s)" enable_values (string_of_enable enable_default_after))

(* ********** *) 

let pdr_qe_action o = flags.pdr_qe <- (pdr_qe_of_string o)
  
let pdr_qe_spec = 
  ("--pdr_qe", 
   Arg.String pdr_qe_action, 
   Format.sprintf "(PDR) choose quantifier elimination algorithm (available: %s, default: %s)" pdr_qe_values (string_of_pdr_qe pdr_qe_default))

(* ********** *) 

let pdr_subs_timeout_action o = flags.pdr_subs_timeout <- o
  
let pdr_subs_timeout_spec = 
  ("--pdr_subs_timeout", 
   Arg.Int pdr_subs_timeout_action, 
   Format.sprintf "(PDR) timeout in ms for subsumption check in frames (default: %s)" (string_of_pdr_subs_timeout pdr_subs_timeout_default))

(* ********** *) 

let pdr_check_inductive_action o = flags.pdr_check_inductive <- o
  
let pdr_check_inductive_spec = 
  ("--pdr_check_inductive", 
   Arg.Bool pdr_check_inductive_action, 
   Format.sprintf "(PDR) Check inductiveness of blocking clauses (default: %s)" (string_of_pdr_check_inductive pdr_check_inductive_default))

(* ********** *) 

let pdr_fwd_prop_check_multi_action o = flags.pdr_fwd_prop_check_multi <- o
  
let pdr_fwd_prop_check_multi_spec = 
  ("--pdr_fwd_prop_check_multi", 
   Arg.Bool pdr_fwd_prop_check_multi_action, 
   Format.sprintf "(PDR) Simultaneous check for forward propagation (default: %s)" (string_of_pdr_fwd_prop_check_multi pdr_fwd_prop_check_multi_default))

(* ********** *) 

let pdr_dump_inductive_assertions_action o = 
  flags.pdr_dump_inductive_assertions <- o
  
let pdr_dump_inductive_assertions_spec = 
  ("--pdr_dump_inductive_assertions", 
   Arg.Bool pdr_dump_inductive_assertions_action, 
   Format.sprintf "(PDR) Output inductive blocking clauses (default: %s)" (string_of_pdr_dump_inductive_assertions pdr_dump_inductive_assertions_default))

(* ********** *) 

let pdr_inductive_assertions_file_action o = 
  flags.pdr_inductive_assertions_file <- Some o
  
let pdr_inductive_assertions_file_spec = 
  ("--pdr_inductive_assertions_file", 
   Arg.String pdr_inductive_assertions_file_action, 
   Format.sprintf "(PDR) Output file for inductive blocking clauses (default: stdout)")

(* ********** *) 

let pdr_minimize_cex_action o = flags.pdr_minimize_cex <- o
  
let pdr_minimize_cex_spec = 
  ("--pdr_minimize_cex", 
   Arg.Bool pdr_minimize_cex_action, 
   Format.sprintf "(PDR) Minimize counterexamples (default: %s)" (string_of_pdr_minimize_cex pdr_minimize_cex_default))

(* ********** *) 

let pdr_tighten_to_unsat_core_action o = flags.pdr_tighten_to_unsat_core <- o
  
let pdr_tighten_to_unsat_core_spec = 
  ("--pdr_tighten_to_unsat_core", 
   Arg.Bool pdr_tighten_to_unsat_core_action, 
   Format.sprintf "(PDR) Tighten blocking clauses to an unsatisfiable core (default: %s)" (string_of_pdr_tighten_to_unsat_core pdr_tighten_to_unsat_core_default))

(* ********** *) 

let pdr_block_in_future_action o = flags.pdr_block_in_future <- o
  
let pdr_block_in_future_spec = 
  ("--pdr_block_in_future", 
   Arg.Bool pdr_block_in_future_action, 
   Format.sprintf "(PDR) Block counterexample in future frames (default: %s)" (string_of_pdr_block_in_future pdr_block_in_future_default))

(* ********** *) 
 
let pdr_prop_in_last_frame_action o = flags.pdr_prop_in_last_frame <- o
  
let pdr_prop_in_last_frame_spec = 
  ("--pdr_prop_in_last_frame", 
   Arg.Bool pdr_prop_in_last_frame_action, 
   Format.sprintf "(PDR) Last frame contains property (Bradley vs. Een et al) (default: %s)" (string_of_pdr_prop_in_last_frame pdr_prop_in_last_frame_default))

(* ********** *) 
 
let cooper_order_var_by_elim_action o = flags.cooper_order_var_by_elim <- o
                                          
let cooper_order_var_by_elim_spec = 
  ("--cooper_order_var_by_elim", 
   Arg.Bool cooper_order_var_by_elim_action, 
   Format.sprintf "(Cooper QE) Order variables in polynomials by order of elimination (available: %s, default: %B)" cooper_order_var_by_elim_values cooper_order_var_by_elim_default)
  
(* ********** *) 
  
let cooper_general_lbound_action o = flags.cooper_general_lbound <- o
                                       
let cooper_general_lbound_spec = 
  ("--cooper_general_lbound", 
   Arg.Bool cooper_general_lbound_action, 
   Format.sprintf "(Cooper QE) Choose lower bounds containing variables (available: %s, default: %B)" cooper_general_lbound_values cooper_general_lbound_default)

(* ********** *) 

let debug_action o = flags.debug <- o :: flags.debug 
  
let debug_spec = 
  ("--debug", 
   Arg.String debug_action, 
   Format.sprintf "enable debug output for a section, give one --debug option for each section to be enabled")

(* ********** *) 

let debug_log_action o = flags.debug_log <- Some o
  
let debug_log_spec = 
  ("--debug-log", 
   Arg.String debug_log_action, 
   Format.sprintf "output debug messages to file (default: stdout)")

(* ********** *) 

let log_level_action o () = flags.log_level <- o
  
let log_level_off_spec = 
  ("-qq", 
   Arg.Unit (log_level_action Event.L_off), 
   Format.sprintf "Disable output completely")

let log_level_fatal_spec = 
  ("-q", 
   Arg.Unit (log_level_action Event.L_fatal), 
   Format.sprintf "Disable output, fatal errors only")

let log_level_error_spec = 
  ("-s", 
   Arg.Unit (log_level_action Event.L_error), 
   Format.sprintf "Silence output, errors only")

let log_level_info_spec = 
  ("-v", 
   Arg.Unit (log_level_action Event.L_info), 
   Format.sprintf "Output informational messages")

let log_level_debug_spec = 
  ("-vv", 
   Arg.Unit (log_level_action Event.L_debug), 
   Format.sprintf "Output informational and debug messages")

let log_level_trace_spec = 
  ("-vvv", 
   Arg.Unit (log_level_action Event.L_trace), 
   Format.sprintf "Output informational, debug and trace messages")

(* ********** *) 

let log_format_xml_action o () = flags.log_format_xml <- o

let log_format_xml_spec = 
  ("-xml", 
   Arg.Unit (log_format_xml_action true), 
   Format.sprintf "Output in XML format")


(* ********************************************************************** *)
(* Pretty-printing of flags                                               *)
(* ********************************************************************** *)


(* ********************************************************************** *)
(* Accessor functions for flags                                           *)
(* ********************************************************************** *)

let timeout_wall () = flags.timeout_wall

let timeout_virtual () = flags.timeout_virtual

let smtsolver () = flags.smtsolver 

let z3_bin () = flags.z3_bin

let cvc4_bin () = flags.cvc4_bin

let enable () = flags.enable 

let pdr_qe () = flags.pdr_qe 

let pdr_subs_timeout () = flags.pdr_subs_timeout 

let pdr_check_inductive () = flags.pdr_check_inductive 

let pdr_fwd_prop_check_multi () = flags.pdr_fwd_prop_check_multi 

let pdr_dump_inductive_assertions () = flags.pdr_dump_inductive_assertions

let pdr_inductive_assertions_file () = flags.pdr_inductive_assertions_file

let pdr_minimize_cex () = flags.pdr_minimize_cex 

let pdr_tighten_to_unsat_core () = flags.pdr_tighten_to_unsat_core 

let pdr_block_in_future () = flags.pdr_block_in_future 

let pdr_prop_in_last_frame () = flags.pdr_prop_in_last_frame 

let cooper_order_var_by_elim () = flags.cooper_order_var_by_elim

let cooper_general_lbound () = flags.cooper_general_lbound

let debug () = flags.debug

let debug_log () = flags.debug_log

let log_level () = flags.log_level

let log_format_xml () = flags.log_format_xml

let input_file () = match flags.input_file with 
  | Some f -> f 
  | None -> failwith "No input file given"


(* ********************************************************************** *)
(* Parsing of command-line options into flags                             *)
(* ********************************************************************** *)

let usage_msg = 
  Format.sprintf 
    "Usage: %s [options] FILE@\nProve properties in Lustre program FILE@\n" 
    (Filename.basename Sys.executable_name)

let rec help_action () = raise (Arg.Help (Arg.usage_string speclist usage_msg))

and speclist = 
  [

    (* Wallclock timeout *)
    timeout_wall_spec;

    (* CPU timeout *)
    timeout_virtual_spec;

    (* Set SMT solver *)
    smtsolver_spec;

    (* Set executable for Z3 solver *)
    z3_bin_spec;

    (* Set executable for CVC4 solver *)
    cvc4_bin_spec;

    (* Set enabled modules *)
    enable_spec;

    (* Set QE in PDR *)
    pdr_qe_spec;

    (* Set timeout for subsumption check in frames in PDR *)
    pdr_subs_timeout_spec;

    (* Check inductiveness of blocking clauses *)
    pdr_check_inductive_spec;

    (* Simultaneous check for propagation *)
    pdr_fwd_prop_check_multi_spec;

    (* Output inductive of blocking clauses *)
    pdr_dump_inductive_assertions_spec;

    (* File for inductive of blocking clauses *)
    pdr_inductive_assertions_file_spec;

    (* Minimize counterexamples *)
    pdr_minimize_cex_spec;

    (* Tighten blocking clauses to an unsatisfiable core *)
    pdr_tighten_to_unsat_core_spec;

    (* Block counterexample in future frames *)
    pdr_block_in_future_spec;

    (* Last frame contains property (Bradley vs. Een et al) *)
    pdr_prop_in_last_frame_spec;

    (* Set option in Cooper QE*)
    cooper_order_var_by_elim_spec;
    cooper_general_lbound_spec;

    (* Enable debug output *)
    debug_spec;

    (* Enable debug output *)
    debug_log_spec;

    (* Set verbosity of output *)
    log_level_error_spec;
    log_level_fatal_spec;
    log_level_off_spec;
    log_level_info_spec;
    log_level_debug_spec;
    log_level_trace_spec;

    (* Set output format to XML *)
    log_format_xml_spec;

    (* Display help *)
    ("-help", 
     Arg.Unit help_action, 
     " Display this list of options");
    ("--help", 
     Arg.Unit help_action, 
     "Display this list of options");
    ("-h", 
     Arg.Unit help_action, 
     "    Display this list of options")
  ]
    

let anon_action s = 
  match flags.input_file with 
    | None -> flags.input_file <- Some s
    | Some _ -> raise (Arg.Bad "More than one input file given")

  
let parse_argv () = 
  
  (* Parse command-line arguments *)
  Arg.parse speclist anon_action usage_msg;
  
  (* Set default value if unchanged *)
  if flags.enable = enable_default_init then 
    flags.enable <- enable_default_after;

  (* Fail if input file not set *)
  match flags.input_file with 
    | None -> 
      Format.printf 
        "%s: No input file given@\n" Sys.argv.(0);
      Arg.usage speclist usage_msg;
      exit 2
    | Some _ -> ()
      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)