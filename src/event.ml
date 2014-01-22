(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

open Lib


(* Termination message received *)
exception Terminate


(* ********************************************************************** *)
(* Events passed on to callers                                            *)
(* ********************************************************************** *)


(* Events exposed to the processes *)
type event = 
  | Invariant of kind_module * Term.t 
  | Proved of kind_module * int option * string 
  | Disproved of kind_module * int option * string 
  | BMCState of int * (string list)


(* Pretty-print a message *)
let pp_print_event ppf = function 

  | Invariant (m, t) -> 

    Format.fprintf 
      ppf 
      "@[<hv>Invariant@ %a@ by %a@]" 
      Term.pp_print_term t
      pp_print_kind_module m

  | Proved (m, k, p) -> 
    Format.fprintf 
      ppf 
      "@[<hv>Proved@ %s@ %tby %a@]" 
      p 
      (function ppf -> match k with 
         | None -> ()
         | Some k -> Format.fprintf ppf "at %d@ " k)
      pp_print_kind_module m

  | Disproved (m, k, p) -> 
    Format.fprintf 
      ppf 
      "@[<hv>Disproved@ %s@ %tby %a@]" 
      p 
      (function ppf -> match k with 
         | None -> ()
         | Some k -> Format.fprintf ppf "at %d@ " k)
      pp_print_kind_module m

  | BMCState (k, p) -> 
    Format.fprintf ppf 
      "@[<hv>BMC status@ k=%d@ %a@]" 
      k 
      (pp_print_list Format.pp_print_string ",@ ") p


(* ********************************************************************** *)
(* Log levels                                                             *)
(* ********************************************************************** *)


(* Levels of log messages *)
type log_level =
  | L_off
  | L_fatal
  | L_error
  | L_warn
  | L_info
  | L_debug
  | L_trace


(* Associate an integer with each level to induce a total ordering *)
let int_of_log_level = function 
  | L_off -> -1 
  | L_fatal -> 0
  | L_error -> 1
  | L_warn -> 2
  | L_info -> 3
  | L_debug -> 4
  | L_trace -> 5

let log_level_of_int = function 
  | -1 -> L_off 
  | 0 -> L_fatal
  | 1 -> L_error
  | 2 -> L_warn
  | 3 -> L_info
  | 4 -> L_debug
  | 5 -> L_trace
  | _ -> raise (Invalid_argument "log_level_of_int")

(* Compare two levels *)
let compare_levels l1 l2 = 
  Pervasives.compare (int_of_log_level l1) (int_of_log_level l2)


(* Current log level *)
let log_level = ref L_warn


(* Set log level *)
let set_log_level l = log_level := l


(* Level is of higher or equal priority than current log level? *)
let output_on_level level = compare_levels level !log_level <= 0


(* Return Format.fprintf if level is is of higher or equal priority
   than current log level, otherwise return Format.ifprintf *)
let ignore_or_fprintf level = 
  if output_on_level level then Format.fprintf else Format.ifprintf


(* ********************************************************************** *)
(* Output target                                                          *)  
(* ********************************************************************** *)


(* Current formatter for output *)
let log_ppf = ref Format.std_formatter


(* Set file to write log messages to *)
let log_to_file f = 

  (* Open channel to logfile *)
  let oc = 
    try open_out f with
      | Sys_error _ -> failwith "Could not open logfile"
  in 
  
  (* Create and store formatter for logfile *)
  log_ppf := Format.formatter_of_out_channel oc


(* Write messages to standard output *)
let log_to_stdout () = log_ppf := Format.std_formatter


(* ********************************************************************** *)
(* Plain text output                                                      *)
(* ********************************************************************** *)


(* Level as string for plain text output *)
let pt_string_of_level = function 
  | L_off -> assert false
  | L_fatal -> "FATAL"
  | L_error -> "ERROR"
  | L_warn -> "WARNING"
  | L_info -> "INFO"
  | L_debug -> "DEBUG"
  | L_trace -> "TRACE"


(* Pretty-print level for plain text output *)
let pp_print_level_pt ppf l = Format.fprintf ppf "%s" (pt_string_of_level l)


(* Kind module as string for plain text output *)
let pt_string_of_kind_module = function
  | `PDR -> "PDR"
  | `BMC -> "BMC"
  | `IND -> "inductive step"
  | `INVGEN -> "invariant generator"
  | `INVMAN -> "invariant manager"
  | `Interpreter -> "interpreter"


(* Pretty-print kind module  for plain text output *)
let pp_print_kind_module_pt ppf m = 
  Format.fprintf ppf "%s" (pt_string_of_kind_module m)


(* Output message as plain text *)
let printf_pt mdl level fmt = 

  (ignore_or_fprintf level)
    !log_ppf 
    (* ("@[<hov>%a (%a):@ " ^^ fmt ^^ "@]@.@.") *)
    ("@[<hov>" ^^ fmt ^^ "@]@.@.") 
    (* pp_print_level_pt level *)
    (* pp_print_kind_module_pt mdl *)
    

(* Output proved property as plain text *)
let proved_pt mdl k prop = 

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    ("@[<hov>Success: Property %s is valid %tin %a@.@.") 
    prop
    (function ppf -> match k with
       | None -> ()
       | Some k -> Format.fprintf ppf "for k=%d " k)
    pp_print_kind_module_pt mdl


(* Output disproved property as plain text *)
let disproved_pt mdl k prop = 

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    ("@[<hov>Failure: Property %s is invalid %tin %a@.@.") 
    prop
    (function ppf -> match k with
       | None -> ()
       | Some k -> Format.fprintf ppf "for k=%d " k)
    pp_print_kind_module_pt mdl


(* Output statistics section as plain text *)
let stat_pt mdl stats =

  Format.fprintf 
    !log_ppf 
    "@[<v>Statistics for %a@,@,%a@]@."
    pp_print_kind_module mdl
    (pp_print_list
       (function ppf -> function (section, items) -> 
          Format.fprintf ppf "[%s]@,%a@," 
            section
            Stat.pp_print_stats items)
       "@,")
    stats



(* Output statistics section as plain text *)
let progress_pt mdl k =

  Format.fprintf 
    !log_ppf 
    "@[<v>Progress in %a: %d@]@."
    pp_print_kind_module mdl
    k

(* ********************************************************************** *)
(* XML output                                                             *)
(* ********************************************************************** *)

(* Level to class attribute of log tag *)
let xml_cls_of_level = function
  | L_off -> assert false
  | L_fatal -> "fatal"
  | L_error -> "error"
  | L_warn -> "warn"
  | L_info -> "info"
  | L_debug -> "debug"
  | L_trace -> "trace"
  

(* Pretty-print level as class attribute of log tag *)
let pp_print_level_xml_cls ppf l = 
  Format.fprintf ppf "%s" (xml_cls_of_level l)


(* Kind module as source attribute of log tag *)
let xml_src_of_kind_module = function
  | `PDR -> "pdr"
  | `BMC -> "bmc"
  | `IND -> "indstep"
  | `INVGEN -> "invgen"
  | `INVMAN -> "invman"
  | `Interpreter -> "interpreter"


(* Pretty-print kind module as source attribute of log tag *)
let pp_print_kind_module_xml_src ppf m = 
  Format.fprintf ppf "%s" (xml_src_of_kind_module m)


(* XML at the beginning the output *)
let print_xml_header () = 

  Format.fprintf 
    !log_ppf 
    "@[<v><?xml version=\"1.0\"?>@,\
     <Results xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">@]@."


(* XML at the end of the output *)
let print_xml_trailer () = 

  Format.fprintf !log_ppf "</Results>@."


(* Output message as XML *)
let printf_xml mdl level fmt = 

  (ignore_or_fprintf level)
    !log_ppf 
    ("@[<hv 2><log class=\"%a\" source=\"%a\">@,@[<hov>" ^^ 
       fmt ^^ 
       "@]@;<0 -2></log>@]@.") 
    pp_print_level_xml_cls level
    pp_print_kind_module_xml_src mdl


(* Output proved property as XML *)
let proved_xml mdl k prop = 

  (* Update time *)
  Stat.update_time Stat.total_time;

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    ("@[<hv 2><Property name=\"%s\">@,\
      <Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@,\
      %t\
      <Answer source=\"%a\">valid</Answer>@;<0 -2>\
      </Property>@]@.") 
    prop
    (Stat.get_float Stat.total_time)
    (function ppf -> match k with 
       | None -> () 
       | Some k -> Format.fprintf ppf "<K>%d</K>@," k)
    pp_print_kind_module_xml_src mdl


(* Output disproved property as XML *)
let disproved_xml mdl k prop = 

  (* Update time *)
  Stat.update_time Stat.total_time;

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    ("@[<hv 2><Property name=\"%s\">@,\
      <Runtime unit=\"sec\" timeout=\"false\">%.3f</Runtime>@,\
      %t\
      <Answer source=\"%a\">invalid</Answer>@;<0 -2>\
      </Property>@]@.") 
    prop
    (Stat.get_float Stat.total_time)
    (function ppf -> match k with 
       | None -> () 
       | Some k -> Format.fprintf ppf "<K>%d</K>@," k)
    pp_print_kind_module_xml_src mdl
  

let rec pp_print_values_xml i ppf = function
  | [] -> ()
  | t :: [] -> Format.fprintf ppf "@[<hv 2><Value time=\"%d\">@,@[<hv 2>%a@]@;<0 -2></Value>@]" i Term.pp_print_term t
  | t :: tl -> Format.fprintf ppf "%a@;<0 -2>%a" (pp_print_values_xml i) [t] (pp_print_values_xml (succ i)) tl


let pp_print_state_var_values_xml ppf (state_var, values) = 

  Format.fprintf 
    ppf
    "@[<hv 2>@[<hv 3><Signal@ name=\"%a\"@ node=\"%s\"@ type=\"%a\">@]@,\
     @[<v 2>%a@]@;<0 -2>\
     </Signal>@]"
    StateVar.pp_print_state_var_original state_var
    "top"
    Type.pp_print_type (StateVar.type_of_state_var state_var)
    (pp_print_values_xml 0) values

(* Output counterexample as XML *)
let counterexample_xml mdl cex = 

  (ignore_or_fprintf L_fatal)
    !log_ppf 
    "@[<hv 2><Counterexample>@,%a@;<0 -2></Counterexample>@]"
    (pp_print_list pp_print_state_var_values_xml "@,") cex
    

(* Output statistics section as XML *)
let stat_xml mdl stats =

  Format.fprintf
    !log_ppf
    "@[<hv 2><stat source=\"%a\">@,%a@;<0 -2></stat>@]@."
    pp_print_kind_module_xml_src mdl
    (pp_print_list
       (function ppf -> function (section, items) ->
          Format.fprintf ppf 
            "@[<hv 2><section>@,<name>%s</name>@,%a@;<0 -2></section>@]"
            section
            Stat.pp_print_stats_xml items)
       "@,")
    stats


(* Output progress as XML *)
let progress_xml mdl k =

  Format.fprintf
    !log_ppf
    "@[<hv 2><progress source=\"%a\">%d@;<0 -2></progress>@]@."
    pp_print_kind_module_xml_src mdl
    k


(* ********************************************************************** *)
(* Relay output to invariant manager                                      *)
(* ********************************************************************** *)


(* Send an event to the log *)
let log (mdl : kind_module) (lvl : log_level) (msg : string) = 

  try 

    (* Send log event message *)
    Messaging.send 
      (Messaging.UserMessage (Messaging.Log (int_of_log_level lvl, msg)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Send message to invariant manager *)
let printf_relay mdl level fmt = 

  Format.kfprintf 
    (function ppf -> 

      let s = Format.flush_str_formatter () in

      if compare_levels level !log_level > 0 then () else
        log mdl level s)

    Format.str_formatter
    fmt


(* Send statistics *)
let stat_relay stats =

  try 

    (* Send statistics message *)
    Messaging.send 
      (Messaging.UserMessage 
         (Messaging.Stat (Marshal.to_string stats [])))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Send progress indicator *)
let progress_relay k =

  try 

    (* Send progress message *)
    Messaging.send 
      (Messaging.UserMessage 
         (Messaging.Progress k))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* ********************************************************************** *)
(* State of the logger                                                    *)
(* ********************************************************************** *)


(* Log formats *)
type log_format = 
  | F_pt
  | F_xml
  | F_relay


(* Current log format *)
let log_format = ref F_pt

(* Set log format to plain text *)
let set_log_format_pt () = log_format := F_pt

(* Set log format to XML *)
let set_log_format_xml () = 

  log_format := F_xml;

  (* Print XML header *)
  print_xml_header ()
               

(* Relay log messages to invariant manager *)
let set_relay_log () = log_format := F_relay


(* ********************************************************************** *)
(* Generic logging functions                                              *)
(* ********************************************************************** *)

(* Log a message with source and log level *)
let log mdl level fmt = 
  match !log_format with 
    | F_pt -> printf_pt mdl level fmt
    | F_xml -> printf_xml mdl level fmt
    | F_relay -> printf_relay mdl level fmt


(* Log a message with source and log level *)
let log_proved mdl k prop =
  match !log_format with 
    | F_pt -> proved_pt mdl k prop
    | F_xml -> proved_xml mdl k prop
    | F_relay -> ()


(* Log a message with source and log level *)
let log_disproved mdl k prop =
  match !log_format with 
    | F_pt -> disproved_pt mdl k prop
    | F_xml -> disproved_xml mdl k prop
    | F_relay -> ()


(* Log a counterexample *)
let log_counterexample mdl cex = 
  match !log_format with 
    | F_pt -> counterexample_xml mdl cex
    | F_xml -> counterexample_xml mdl cex
    | F_relay -> ()


(* Output statistics of a section of a source *)
let stat mdl stats =
  match !log_format with 
    | F_pt -> stat_pt mdl stats
    | F_xml -> stat_xml mdl stats
    | F_relay -> stat_relay stats
  

(* Output progress indicator of a source *)
let progress mdl k = 
  match !log_format with 
    | F_pt -> ()
    | F_xml -> progress_xml mdl k
    | F_relay -> progress_relay k
  

(* Terminate log output *)
let terminate_log () = 
  match !log_format with 
    | F_pt -> ()
    | F_xml -> print_xml_trailer ()
    | F_relay -> ()


(* ********************************************************************** *)
(* Initialization for the messaging system                                *)
(* ********************************************************************** *)


(* Setup of the messaging: context and sockets of the invariant
   manager, ports to connect to for the workers *)
type messaging_setup = 
  (Messaging.ctx * Messaging.socket * Messaging.socket) * (string * string)

type mthread = Messaging.thread

(* Create contexts and bind ports for all processes *)
let setup () = 

  (* Create context for invariant manager *)
  let im_context, (b, m) = Messaging.init_im () in

  (* Return contexts *)
  (im_context, (b, m))


(* Start messaging for a process *)
let run_process proc (_, (bcast_port, push_port)) on_exit = 

  (* Initialize messaging for process *)
  let ctx = Messaging.init_worker proc bcast_port push_port in

  (* Run messaging for process *)
  Messaging.run_worker ctx proc on_exit


(* Start messaging for invariant manager *)
let run_im (ctx, _) pids on_exit = 
  Messaging.run_im ctx pids on_exit


(* ********************************************************************** *)
(* Events                                                                 *)
(* ********************************************************************** *)


(* Broadcast an invariant *)
let invariant mdl (term : Term.t) = 
  
  (* Serialize term to string *)
  let term_string = Marshal.to_string term [Marshal.No_sharing] in

  try
    
    (* Send invariant message *)
    Messaging.send 
      (Messaging.InvariantMessage 
         (Messaging.INVAR (term_string, 0)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast a disproved property *)
let disproved mdl k prop = 

  (* Output property as disproved *)
  log_disproved mdl k prop;

  try

    (* Send invariant message *)
    Messaging.send 
      (Messaging.InvariantMessage 
         (Messaging.DISPROVED 
            (prop, 
             (match k with None -> -1 | Some k -> k), 
             0)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast a proved property as an invariant *)
let proved mdl k (prop, term) = 

  (* Output property as proved *)
  log_proved mdl k prop;

  try

    (* Send invariant message *)
    Messaging.send 
      (Messaging.InvariantMessage 
         (Messaging.PROVED 
            (prop, 
             (match k with None -> -1 | Some k -> k), 
             0)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast status of BMC *)
let bmcstate k props =

  try

    (* Send BMC status message *)
    Messaging.send 
      (Messaging.InductionMessage 
         (Messaging.BMCSTATE (k, props)))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()


(* Broadcast termination message *)
let terminate () = 

  try

    (* Send termination message *)
    Messaging.send (Messaging.ControlMessage Messaging.TERM);

    minisleep 0.1

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> ()



(* ********************************************************************** *)
(* Receiving events                                                       *)
(* ********************************************************************** *)


(* Receive all queued messages *)
let recv () = 

  try

    List.fold_left 
      (function accum -> 
        (function 

          (* Terminate on TERM message *)
          | _, Messaging.ControlMessage Messaging.TERM -> raise Terminate

          | mdl, Messaging.UserMessage (Messaging.Log (lvl, msg)) ->

            (debug event 
                "Received LOG message %s"
                msg
             in
             
             log mdl (log_level_of_int lvl) "%s" msg; 
             
             accum)

          | mdl, Messaging.UserMessage (Messaging.Stat stats) -> 

            stat 
              mdl 
              (Marshal.from_string stats 0 : 
                 (string * Stat.stat_item list) list);

            accum

          | mdl, Messaging.UserMessage (Messaging.Progress k) -> 

            progress mdl k;

            accum

          (* Drop control messages *)
          | _, Messaging.ControlMessage _ 
          | _, Messaging.InvariantMessage (Messaging.RESEND _) -> accum 

          (* Pass BMC status messages *)
          | _, Messaging.InductionMessage (Messaging.BMCSTATE (k, props)) -> 

            BMCState (k, props) :: accum

          (* Pass invariant messages as term without serial number *)
          | mdl, Messaging.InvariantMessage (Messaging.INVAR (f, _)) ->

            (* Hashcons term *)
            let t = Term.import (Marshal.from_string f 0 : Term.t) in 

            Invariant (mdl, t) :: accum

          (* Pass disproved messages as string without serial number *)
          | mdl, Messaging.InvariantMessage (Messaging.PROVED (p, k, _)) ->

            Proved (mdl, (if k < 0 then None else Some k), p) :: accum

          (* Pass disproved messages as string without serial number *)
          | mdl, Messaging.InvariantMessage (Messaging.DISPROVED (p, k, _)) ->

            Disproved (mdl, (if k < 0 then None else Some k), p) :: accum

        )
      )
      []
      (List.rev (Messaging.recv ()))

  (* Don't fail if not initialized *) 
  with Messaging.NotInitialized -> []


let exit t = Messaging.exit t


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
