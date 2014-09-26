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

(** Common functions 

    @author Jason Oxley, Christoph Sticksel **)


(* ********************************************************************** *)
(* Static constants and defaults                                          *)
(* ********************************************************************** *)

(* TODO: Put this in a config file *)

(* Data directory of Ocsigen instance *)
let data_dir = Ocsigen_config.get_datadir ()

(* Path to generated input and output files *)
let jobs_dir = Filename.concat data_dir "jobs"

(* Maximum one minute load average *)
let load1_max = 8.

(* Maximum five minutes load average *)
let load5_max = 4.

(* Maximum 15 minutes load average *)
let load15_max = 0.

(* Purge jobs after one day *)
let job_purge_time =  86400.

(* ********************************************************************** *)
(* Executables and parameters                                             *)
(* ********************************************************************** *)


(* Map of identifiers to executables *)
let checkers_and_arguments =

  [

    (* Kind 2 *)
    ("kind2", 
     ("/usr/local/bin/kind2", 
      ["-xml"]));

    (* PKind *)
    ("pkind", 
     ("/usr/local/bin/pkind", 
      ["-xml"; "-xml-to-stdout"]));
    
    (* JKind 

       TODO: JKind does not output to stdout, but into a .xml file *)
    ("jkind",
     ("/usr/local/bin/jkind", 
      ["-xml"]))
       
  ]


(* Map of identifiers to executables *)
let interpreters_and_arguments =

  [

    (* Kind 2 *)
    ("kind2", 
     ("/usr/local/bin/kind2", 
      ["-xml"; "--enable"; "interpreter"]))

  ]


(* Return executable and combine arguments with defaults *)
let cmd_and_args cmd_and_args key args = 

  (* Get executable and default arguments *)
  let cmd, default_args = 
    List.assoc key cmd_and_args 
  in

  (* Reverse and filter out empty strings *)
  let args' = List.filter ((<>) "") (List.rev args) in

  (* Return excutable and arguments *)
  (cmd, (default_args @ args'))


(* Return executable and combine arguments with defaults *)
let checker_cmd_and_args checker args = 
  cmd_and_args checkers_and_arguments checker args


(* Return executable and combine arguments with defaults *)
let interpreter_cmd_and_args interpreter args = 
  cmd_and_args interpreters_and_arguments interpreter args



(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)

(* Pretty-print a format string with custom pretty-printers

   Built-in since OCaml 4.0.1, copied from the sources for earlier
   versions *)
let asprintf fmt =
  let b = Buffer.create 512 in
  let k ppf =
    Format.pp_print_flush ppf ();
    Buffer.contents b
  in
  let ppf = Format.formatter_of_buffer b in
  Format.kfprintf k ppf fmt


(* Pretty-print into a string *)
let string_of_t pp t =

  (* Create a buffer *)
  let buf = Buffer.create 80 in
  
  (* Create a formatter printing into the buffer *)
  let ppf = Format.formatter_of_buffer buf in

  (* Output into buffer *)
  pp ppf t;
  
  (* Flush the formatter *)
  Format.pp_print_flush ppf ();
  
  (* Return the buffer contents *)
  Buffer.contents buf


(* Pretty-print a list *)
let rec pp_print_list pp sep ppf = function

  (* Output nothing for the empty list *)
  | [] -> ()

  (* Output a single element in the list *)
  | e :: [] ->
    pp ppf e

  (* Output a single element and a space *)
  | e :: tl ->

    (* Output one element *)
    pp_print_list pp sep ppf [e];

    (* Output separator *)
    Format.fprintf ppf sep;

    (* Output the rest of the list *)
    pp_print_list pp sep ppf tl


(* Output a time *)
let pp_print_time ppf time =

  (* Month names *)
  let months = [ "Jan"; "Feb"; "Mar"; "Apr"; "May"; "Jun";
                 "Jul"; "Aug"; "Sep"; "Oct"; "Nov"; "Dec" ]
  in

  (* Split local time into components *)
  let
    { Unix.tm_sec = tm_sec;
      Unix.tm_min = tm_min;
      Unix.tm_hour = tm_hour;
      Unix.tm_mday = tm_mday;
      Unix.tm_mon = tm_mon;
      Unix.tm_year = tm_year;
      Unix.tm_wday = tm_wday;
      Unix.tm_yday = tm_yday } =
    
    Unix.localtime time

  in
  
  (* Output as "[Jan 01 00:00:00]" *)
  Format.fprintf
    ppf
    "%s %02d %02d:%02d:%02d"
    (List.nth months tm_mon)
    tm_mday
    tm_hour
    tm_min
    tm_sec


(* String representation of time *)
let string_of_time = string_of_t pp_print_time


(* Output a timestamp *)
let pp_print_timestamp ppf =
  pp_print_time ppf (Unix.gettimeofday ())


(* Pretty-print status of a process *)
let pp_print_process_status ppf = function 
  | Unix.WEXITED e -> Format.fprintf ppf "exited with %d" e
  | Unix.WSIGNALED s -> Format.fprintf ppf "killed with %d" s
  | Unix.WSTOPPED s -> Format.fprintf ppf "stopped with %d" s


(* Server logfiles *)
type server_log = 
  | AccessLog
  | ErrorLog
  | WarningLog


(* Log a message to the given logfile *)
let log l fmt =

  (* Create buffer for output of message *)
  let b = Buffer.create 80 in

  (* Formatter printing into the buffer *)
  let ppf = Format.formatter_of_buffer b in

  (* Continuation after printing to formatter *)
  let k ppf =

    (* Flush the pretty-printer to the buffer *)
    Format.pp_print_flush ppf ();

    (* Get string contents of buffer *)
    let s = Buffer.contents b in

    (* Write string as log message to the chosen logfile *)
    match l with 
      | AccessLog -> Ocsigen_messages.accesslog s
      | ErrorLog -> Ocsigen_messages.errlog s
      | WarningLog -> Ocsigen_messages.warning s

  in

  (* Print message to log with continuation *)
  Format.kfprintf k ppf fmt
    
       


(* ********************************************************************** *)
(* Unique identifiers *)
(* ********************************************************************** *)


(* Get base l string representation of integer n *)
let base10tol n =

  (* Characters to use *)
  let digits =
    [|
      '0';'1';'2';'3';'4';'5';'6';'7';'8';'9';
      'A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';
      'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z';
      (* 'a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';
         'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z' *)
    |]
  in

  (* l is number of characters *)
  let base = Int64.of_int (Array.length digits) in

  (* Convert to base l *)
  let rec base_iter acc n =

      if Int64.(n = zero) then acc else

        base_iter
          ((String.make 
              1
              (Array.get digits Int64.(to_int (rem n base)))) ^ acc)
          Int64.(div n base)
  in

  (* Conver n to a base l string *)
  base_iter "" n


(* ********************************************************************** *)
(* File input and output                                                  *)
(* ********************************************************************** *)


(* Read a file and return lines as string list *)
let read_file filename = 

  (* Buffer to write lines to *)
  let lines = ref [] in
  
  (* Open file for reading *)
  let chan = open_in filename in
  
  try
    
    (* Read until interrupted *)
    while true;
    do
      
      (* Put line at beginning of list *)
      lines := input_line chan :: !lines

    done;

    (* Unreachable, close file just in case *)
    close_in chan;
    
    (* Return empty list *)
    []

  (* Reached end of file *)
  with End_of_file ->
  
    (* Close file *)
    close_in chan;
    
    (* Return lines in original order *)
    List.rev !lines


(* Read bytes from file, starting at given position *)
let read_bytes start filename =

  (* Open file *)
  let ic = open_in_bin filename in

  (* Get length of bytes available to read *)
  let n = (in_channel_length ic) - start in

  (* Characters available to read after start? *)
  if n > 0 then

    (

      (* Go to starting position in file *)
      seek_in ic start;

      (* Create string of fixed size *)
      let s = String.create n in

      (* Read into string *)
      really_input ic s 0 n;

      (* Close input channel *)
      close_in ic;

      (* Return new position and string *)
      (start + n, s)

    )

  else

    (

      (* Close input channel *)
      close_in ic;

      (* Position is unchanged, string is empty *)
      (start, "")

    )


(* Create string identifier for job from request id *)
let generate_uid () = 
  let req_id = Eliom_request_info.get_request_id () in
  base10tol Int64.(logand req_id (of_int32 Int32.max_int))


(* Get load average in a pseudo-portable way

   Try /proc/loadavg first (Linux), then execute sysctl -n vm.loadavg (Mac OS X) *)
let get_loadavg () =

  try 

    (* Open load averages file *)
    let loadavg_ch = open_in "/proc/loadavg" in
    
    (* Read load averages from file *)
    let load1, load5, load15 =
      Scanf.fscanf loadavg_ch "%f %f %f" (fun l1 l5 l15 -> (l1,l5,l15))
    in
    
    (* Close load averages file *)
    close_in loadavg_ch;
    
    (* Return load averages *)
    load1, load5, load15

  (* /proc/loadavg not available *)
  with Sys_error _ -> 

    (* Run sysctl command *)
    let loadavg_ch = Unix.open_process_in "sysctl -n vm.loadavg" in

    (* Read load averages from command output *)
    let load1, load5, load15 =
      Scanf.fscanf loadavg_ch "{ %f %f %f }" (fun l1 l5 l15 -> (l1,l5,l15))
    in
    
    (* Close load averages file *)
    let _ = Unix.close_process_in loadavg_ch in
    
    (* Return load averages *)
    load1, load5, load15

    

