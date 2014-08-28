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

(** Bounded model checking

    @author Christoph Sticksel, Paul Meng
*)

(** Bounded model checking for properties on the transition system *)

(** SMT Solver used for BMC *)
module S : SolverMethods.S

(** Check which properties are true in k steps 

   If [check_ts_props] is true, check in received messages whether
   another process has proved or disproved a named property, and remove
   it. Otherwise, discard messages from other processes about
   properties.

   This function does not have side effects such as sending messages,
   thus can safely be called to check properties not in the transition
   system.
*)
val bmc_step : bool -> S.t -> TransSys.t -> Numeral.t -> (string * Term.t) list -> (string * Term.t) list * ((StateVar.t * Term.t list) list * (string * Term.t) list) list

(** Entry point *)
val main : TransSys.t -> unit

(** Cleanup before exit *)
val on_exit : TransSys.t option -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
