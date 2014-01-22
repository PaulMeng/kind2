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



(* Seconds before sending the next invariant *)
let period = 0.5


(* We don't need to clean up anything *)
let on_exit () = ()


(* Generate the k-th tautological invariant: a conjunction of k+1
   [true] constants. *)
let mk_inv k = 

  (* Tail-recursive function with accumulator *)
  let rec mk_inv' accum = function 

    (* Base case  *)
    | k when k <= 0 -> 

      (match accum with 
        | [] -> Term.t_true
        | l -> Term.mk_and (Term.t_true :: accum))

    (* Add [true] to accumulator and recurse for k-1 *)
    | k -> mk_inv' (Term.t_true :: accum) (pred k)

  in

  (* Call recursice function with empty accumulator *)
  mk_inv' [] k


(* Send the k-th tautological invariant *)
let rec inv_gen_dummy k = 

  (* Wait before sending an invariant *)
  minisleep period;

  (* Generate the k-th tautological invariant *)
  let inv = mk_inv k in 

  Event.log 
    `INVGEN 
    Event.L_debug 
    "Sending invariant %d: %a" 
    k 
    Term.pp_print_term inv;

  (* Broadcast the invariant *)
  Event.invariant `INVGEN inv;

  (* Recurse for the next invariant *)
  inv_gen_dummy (succ k)
	
(*Sending invariant*)
let send_invariant x  =
  debug il_inv 
    "debuging il formula: @\n%a@\n"
    OldParser.pp_print_il_formula x in
  let invariant = OldParser.il_formula_to_term false x in
	
  debug il_inv "il_formula to invariant@ %a" Term.pp_print_term invariant in
	
	if
	  List.exists(
			fun v -> 
				(int_of_numeral (Var.offset_of_state_var_instance v)) = 1
    ) (TransSys.vars_of_term invariant)
	then
		(
			debug il_inv "****************@ %a" Term.pp_print_term (TransSys.bump_state (-1) invariant) in
			Event.invariant `INVGEN (TransSys.bump_state (-1) invariant);
		)
	else
		(
			Event.invariant `INVGEN invariant
		)
		
	
(* Entry point *)
let main _ = 

  (* Run loop *)
  (*Kind1.Lus_assertions.get_assertion_term; ()*)
  if(Kind1.Solvers_path.yicesw_path = "no") then
	      (
		 Kind1.Globals.my_solver#set (new Kind1.Solver_yices_cmdline.solver_yices_cmdline)
	      )else(
		Kind1.Globals.my_solver#set (new Kind1.Solver_yices.solver_yices)
	      );
  
  Kind1.OldFlags.do_scratch := false;
  if !Kind1.OldFlags.do_scratch then
    begin
    	Kind1.Channels.inv_ch := open_out ((Flags.input_file ())^"."^Kind1.Globals.my_solver#get#file_extension^"_inv_offline")
    end;
  Kind1.OldFlags.invariant_int := true;
  Kind1.OldFlags.invariant_bool := true;
  Kind1.OldFlags.mode_inv := true;
  Kind1.Kind_inv_loop.mainloop (Flags.input_file ()) send_invariant;
  


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
