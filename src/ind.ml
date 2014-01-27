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
   
(* In the step case checking for k-induction, the properties are categorized
   into 3 lists. Goals are the ones not been proved so far. Candidates
   are the ones proven for the step case and needs to be confirmed by the 
   base case. Proved properties are proved in both step case and base case. *)

open Lib

(* Use configured SMT solver *)
module INDSolver = SMTSolver.Make (Config.SMTSolver)

(* High-level methods for BMC solver *)
module S = SolverMethods.Make (INDSolver)

(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)

(* Current step in bmc. *)
let bmc_state = ref 0

(* Invariants received so far. *)
let invs = ref []

(* Solver instance if created *)
let ref_solver = ref None

(* Output statistics *)
let pp_print_stat ppf = 

  Format.fprintf
    ppf
    "Statistics of %a module:@.@.%t@.%t@.%t"
    pp_print_kind_module `IND
    Stat.pp_print_misc_stats
    Stat.pp_print_ind_stats
    Stat.pp_print_smt_stats


(* Clean up before exit *)
let on_exit () =

  (* Stop all timers *)
  Stat.ind_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  Event.stat 
    `IND 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.ind_stats_title, Stat.ind_stats;
     Stat.smt_stats_title, Stat.smt_stats];

  (* Delete solver instance if created *)
  (try 
     match !ref_solver with 
       | Some solver -> 
         S.delete_solver solver; 
         ref_solver := None
       | None -> ()
   with 
     | e -> 
       Event.log `IND Event.L_error 
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))



(* Filter the properties in the goal list. All the properties which are 
   k-inductive (k is a specific number given as an argument) is proved and added 
   into the second element of the returned pair. All the properties which are 
   not k-inductive is returned in the first element of the returned pair. 
   
   Assumption: The conjuction of the properties in goal_pairs should be invalid 
   in the kth step, and there is a check-sat query returning SAT right before 
   calling this function. 
   
   Invariant: The union of the two elements in the returned pair should be the 
   same as the union of goal_pairs and candidate_infos. candidate_infos contains
   the candidate property and the in which step it is proven. Generally, we are
   re-categorizing the properties within goals and candidates  *)
let rec filter_goal_list solver ts k goal_pairs candidate_infos =

  (* if there is no goal to check, return immediately. *)
  if (List.length goal_pairs = 0) then 
    ([], candidate_infos)
    
  else
  (
    (* Instantiate the goals with step k. *)
    let k_goal_pairs = 
      List.map 
        (fun (goal_name, goal_prop) -> 
          (goal_name, TransSys.bump_state k goal_prop)) 
        goal_pairs
    in
  
    (* Get all the variable of the goal. *)
    let concrete_var_list =
      TransSys.vars_of_term (Term.mk_and (List.map snd k_goal_pairs))
    in
  
   (* Get the smt model faultifying the conjuncted goal. *)
   let model = S.get_model solver concrete_var_list in
  
    (* Abstract the model so that it corresponds with the properties which 
       contain only initial state *)
        
		 let abstract_model = List.map (
      fun (var, value) -> 
      ((Var.bump_offset_of_state_var_instance 
          (Numeral.of_int (-1 * k)) var),
        value)
    ) model 
    in
    (*
    (debug ind
      "@[<hv>The model is:@ @[<hv>%a@]@]@."
      CooperQE.pp_print_model
      abstract_model 
      end);
    *)
              
    (* Put the properties satisfying the model into potential_candidate_pairs.
       Put the properties faultifying the model into goal_pairs. *)
    let (potential_candidate_pairs, goal_pairs') = 
      List.partition (
        fun (goal_name, goal_prop) -> 
          Eval.bool_of_value (Eval.eval_term (TransSys.bump_state k goal_prop) model)
      ) ts.TransSys.props 
    in
      
    (* If all the properties are faultified by the counterexample, nothing is
       added into the candidate list, the goals remains in the goal list to
       be checked for a bigger k. *)
    if (List.length potential_candidate_pairs = 0) then
      (goal_pairs, candidate_infos)
      
    else

    (* Instantiate the potential_candidate_pairs with current step. *)
    let k_potential_candidate_pairs = 
      List.map (
        fun (pc_name, pc_prop) -> 
          (pc_name, TransSys.bump_state k pc_prop)
      ) potential_candidate_pairs 
    in
      
    (* Conjunct the potential candidate properties. *)
    let k_conjuncted_potential_candidate = 
      (Term.mk_and (List.map snd k_potential_candidate_pairs)) 
    in

    (* Check conjuncted potential candidate properties. *)
    S.assert_term solver (Term.mk_not k_conjuncted_potential_candidate);
    
    if (S.check_sat solver) then
    (
      (* If the only potential candidate properties doesn't hold, All the 
         properties have been disproved for this iteration. *) 
      if (List.length potential_candidate_pairs = 1) then 
        (goal_pairs, candidate_infos)
              
      else
      (
        (* Filter out all the properties which has been disproved in this
           iteration, and filter again. Then put all the proved properties
           into the candidate list. *)
        let (refined_goals, refined_candidates) = 
          filter_goal_list 
            solver 
            ts 
            k
            potential_candidate_pairs
            candidate_infos 
        in
          
        (* Add all the properties which has been disproved in this
           iteration with those disproved thoughout all the iterations of
           filtering as the goal to prove. Put others as candidates. *)
        (List.rev_append goal_pairs' refined_goals, refined_candidates)
      )
    
    )
    
    (* If the potential candidate properties holds, add all the 
       potential_candidate_infos into the candidates. *)
    else
    (
      (debug ind
        "All good properties proved, proceed with remaining properties"
        end);
        
      let potential_candidate_infos =
        List.map (
          fun potential_candidate_pair ->
            (potential_candidate_pair, k)
        ) potential_candidate_pairs 
      in

      (goal_pairs', 
        List.rev_append potential_candidate_infos candidate_infos)
    )       
  )


let rec ind solver ts k goal_pairs candidate_infos premises invariants_1 premises_1 = 

  Event.log `IND Event.L_info "Inductive step loop at k=%d" k;

  Event.progress `BMC k;

  Stat.set k Stat.ind_k;

  Stat.update_time Stat.ind_total_time; 



  (* Event.log 1 "%t@." pp_print_stat; *)

  (*
  if (k > 10) then

    failwith "For test purpose, induction case check goes up to 10 steps."

  else
  *)
  
  (* Prepare to receive new invariants. *)
  let new_invariants = ref [] in
  
  (* Receiving messages. *)
  let messages = Event.recv () in
  
  (* Terminate when ControlMessage TERM is received.
     
     Add all the new invariants. 
     
     Restart when some goal property is disproved. *)
  List.iter (
    fun message ->
      match message with
      
        (* Add invariant to a temparary list when it's received. *)
        | (Event.Invariant (_, invar)) ->
          ();
        
        (* FIXME *)
        (* We only need to look at the lastest BMCSTATE message. *)
        (* Restart when some goal property is disproved. *)
        | Event.BMCState (bmc_k, disproved_pn_list) ->
      
          (debug ind
            "BMC message of step %d received"
            bmc_k
            end);

          Event.log `IND Event.L_debug
            "BMC message of step %d received"
            bmc_k;

          (* If there are any property in goal_pairs is disproved, step case
             has to restart. *)
          let reset =
            List.exists 
              (fun x -> List.mem x (List.map fst goal_pairs)) 
              disproved_pn_list
          in
        
          if (reset) then
          (
            (* Remove all the disproved property pairs, and restart step case. *)
            let goal_pairs' = 
              List.filter (
                fun (prop_name, prop) -> 
                  not (List.mem prop_name disproved_pn_list)
              ) goal_pairs
            in

            let reset_premises = List.append (List.map snd goal_pairs) !invs in
            restart ts goal_pairs' reset_premises invariants_1 premises_1
          )
          
          (* Nothing in goal_pair is disproved for now record which state is bmc 
             in. *)
          else
            bmc_state := bmc_k
        
        (* Irrelevant message received. *)
        | _ ->
          ()
        
  ) messages;
  
  (* Add invariants to the premises. *)
  let premises' = List.rev_append !new_invariants premises in
  
  
  (* When all the goals have been proven in step case. *)
  if (List.length goal_pairs = 0) then
  (
    (* When bmc has already proven the base case for k induction, the work is 
       done. *)
    if (!bmc_state >= k) then
    (
      (*
      (* All the goals become candidates, store the new candidate and the step 
         in which they are proved. *)
      let all_candidate_infos = 
        List.rev_append 
          (List.map (fun x -> (x, k)) goal_pairs) 
          candidate_infos
      in
      *)

      let all_candidate_pairs = List.map fst candidate_infos in

      (* Send the invariant. *)
      (* Event.invariant 
        (Term.mk_and (List.map snd all_candidate_pairs)); *)
        
      List.iter (Event.proved `IND (Some k)) all_candidate_pairs;

(*
      (* Print out all the properties being proved. *)
      List.iter 
        (
          fun (cdd_prop_name, cdd_prop) -> 
            Event.log 
              0
              "Property %s proved for k = %d "
              cdd_prop_name
              k
        ) all_candidate_pairs;

      ()
*)

    )

    (* When bmc is slower than the step case, run the same procedure with the 
       same k to wait for the bmc to reach k. *)
    else 
    (
      try 

      while (true) do
      (
				(debug ind
         "looping here!"
          end);
        (* Wait for 0.5 seconds. *)
        Lib.minisleep 0.5;

        (* Prepare to receive new invariants. *)
        let new_invariants = ref [] in
  
        (* Receiving messages. *)
        let messages = Event.recv () in

        (* Terminate when ControlMessage TERM is received.
     
           Add all the new invariants. 
     
           Break the while loop and end the step case check when the bounded 
           model checking has catched up. *)

        List.iter (
          fun message ->
            match message with
      
              (* Add invariant to a temparary list when it's received. *)
              | (Event.Invariant (_, invar)) ->
                ();
        
              (* FIXME *)
              (* We only need to look at the lastest BMCSTATE message. *)
              (* Restart when some goal property is disproved. *)
              | Event.BMCState (bmc_k, disproved_pn_list) ->

                (debug ind
                  "BMC message of step %d received"
                  bmc_k
                  end);

                Event.log `IND Event.L_debug
                  "BMC message of step %d received"
                  bmc_k;

                (* If there are any property in goal_pairs is disproved, step case
                   has to restart. *)
                let reset =
                  List.exists 
                    (fun x -> List.mem x (List.map fst goal_pairs)) 
                      disproved_pn_list
                in
								bmc_state := bmc_k;
                if (reset) then
                (
                  (* Remove all the disproved property pairs, and restart step 
                     case. *)
                  let goal_pairs' = 
                    List.filter (
                      fun (prop_name, prop) -> 
                        not (List.mem prop_name disproved_pn_list)
                    ) goal_pairs
                  in

                  let reset_premises = 
                    List.append (List.map snd goal_pairs) !invs 
                  in

                  restart ts goal_pairs' reset_premises invariants_1 premises_1
                )
          
                (* Nothing in goal_pair is disproved for now record which state 
                   is bmc in. *)
                else (

                  

                  if (!bmc_state >= k) then
                  (
										debug ind
          					"3. Enter here!!!!!!!!"
          					end;
                    let all_candidate_pairs = List.map fst candidate_infos in
										
										List.iter 
                    (
                     fun (cdd_prop_name, cdd_prop) -> 
                     debug ind
                     "#############Property %s proved for k = %d "
                     cdd_prop_name
                     k
                     end) all_candidate_pairs;

                    (* Send the invariant. *)

                    List.iter (Event.proved `IND (Some k)) all_candidate_pairs;

(*
                    (* Print out all the properties being proved. *)
                    List.iter 
                    (
                      fun (cdd_prop_name, cdd_prop) -> 
                        Event.log 
                        0
                        "Property %s proved for k = %d "
                        cdd_prop_name
                        k
                    ) all_candidate_pairs;
              
*)
                    raise Exit;
                  )
                )

              (* Irrelevant message received. *)
              | _ ->
                ()

        ) messages;
      ) done

      with
      
      (* When the while loop breaks. *)
      | Exit -> ()

    )
  )
  else
  
  (* Instantiate the premises. *)
  let k_premise' = TransSys.bump_state k (Term.mk_and premises') in
  

  (* Instantiate the goals with step k. *)
  let k_goal_pairs = 
    List.map 
      (fun (goal_name, goal_prop) -> 
        (goal_name, TransSys.bump_state k goal_prop)) 
      goal_pairs 
  in
  
  (* Conjunct the goals of step k. *)
  let k_conjuncted_goal = (Term.mk_and (List.map snd k_goal_pairs)) in
  
  (* Check if the counjuction of the goal properties holds in kth step. *)
  S.push solver;
  
  S.assert_term solver (Term.mk_not k_conjuncted_goal);
  
  (* If the formula is satisfiable, the implication does not hold. *)
  if (S.check_sat solver) then
  (

    (* When there is only one goal left. *)
    if (List.length goal_pairs = 1) then
    (
      
      (* Push the premises for the kth step and transition function from the
         kth step to (k + 1)th step T(k, k + 1), and then check for (k + 1) 
         steps. *)
         
      S.pop solver;
      
      S.assert_term solver k_premise';
      
      S.assert_term solver (TransSys.constr_of_bound (k + 1) ts);
      
			ts.TransSys.props <- invariants_1@(ts.TransSys.props);
      ind solver ts (k + 1) goal_pairs candidate_infos premises' [] []
        
    )
      
    else
    (
    
      (* Filter out all the goals which doesn't hold for the kth step. *)
      let (goal_pairs', candidate_infos') = 
        filter_goal_list solver ts k goal_pairs candidate_infos in
      
      (* If all the goals are faultified in this step. *)
      if (List.length goal_pairs' = 0) then
      (

        (* Unreachable code. *)
        failwith "Unreachable code in ind"
      )
      
      (* If not all the goals are faultified in this step. *)
      else
      (
           
        (* Push the premises for the kth step and transition function from the
           kth step to (k + 1)th step T(k, k + 1), and then check for (k + 1) 
           steps. *)
           
        S.pop solver;
        
        S.assert_term solver k_premise';
        
        S.assert_term solver (TransSys.constr_of_bound (k + 1) ts);       
        
				ts.TransSys.props <- invariants_1@ts.TransSys.props;
        ind solver ts (k + 1) (goal_pairs'@invariants_1) candidate_infos' (premises'@premises_1) [] []
        
      )
    )
  )
  
  (* The conjunction of the goal properties holds. *)
  else
  (

    (* Print out all the properties that becomes a candidate. *)
    List.iter 
    (
      fun (goal_prop_name, goal_prop) -> 
        (debug ind
          "Property %s proved in induction case for k = %d,\ 
           and becomes a candidate"
          goal_prop_name
          k
          end)
    ) k_goal_pairs;

    List.iter 
    (
      fun (goal_prop_name, goal_prop) -> 
        Event.log `IND Event.L_info
          "Property %s proved in induction case for k = %d, \ 
           and becomes a candidate"
          goal_prop_name
          k
    ) k_goal_pairs;

    (* All the goals become candidates, store the new candidate and 
         the step in which they are proved. *)
    let all_candidate_infos = 
      List.rev_append 
        (List.map (fun x -> (x, k)) goal_pairs) 
        candidate_infos
    in

    (* Check if bmc has already proven the base case for k induction. *)
    if (!bmc_state >= k) then

      (
				debug ind
          "1. Enter here!!!!!!!!"
          end;
      
        let all_candidate_pairs = List.map fst all_candidate_infos in
      
        (* Send the invariant. *)

        List.iter (Event.proved `IND (Some k)) all_candidate_pairs;

        TransSys.log_property_valid "inductive step" (List.map fst all_candidate_pairs);
 
(*
        (* Print out all the properties being proved. *)
        List.iter 
        (
          fun (cdd_prop_name, cdd_prop) -> 
            Event.log 
              0
              "Property %s proved for k = %d "
              cdd_prop_name
              k
        ) all_candidate_pairs;
      
        ()
*)
      )

    else (
			debug ind
          "2. Enter here!!!!!!!!"
          end;
      ind solver ts k [] all_candidate_infos premises' [] []
			)
)

and restart ts prop_pairs premises invariants_1 premises_1 = 
    
    Event.log `IND Event.L_info "Restarting inductive step";
  
  (* Delete solver instance *)
  (match !ref_solver with 
    | Some s -> S.delete_solver s
    | None -> ());

  init ts prop_pairs premises invariants_1 premises_1


and init transSys prop_pairs premises invariants_1 premises_1=

    (* Determine logic for the SMT solver *)
    let logic = TransSys.get_logic transSys in

    (* Create solver instance *)
    let solver = 
      S.new_solver ~produce_assignments:true logic
    in
  
    (* Create a reference for the solver. Only used in on_exit. *)
    ref_solver := Some solver;

    (* Push the properties in step 0, and the transition function from 0th step 
       to 1st step T(0, 1), and then begin the check. *)
    S.assert_term solver (Term.mk_and premises);
  
    S.assert_term solver (TransSys.constr_of_bound 1 transSys);
      
    ind solver transSys 1 prop_pairs [] premises invariants_1 premises_1


(* Entry point *)
let main transSys =

  Stat.start_timer Stat.ind_total_time;
	let invariants_1 = ref [] in 
	let premises_1 = ref [] in 
	let flag = ref true in
	let counter = ref 0 in
  (* Terminate when ControlMessage TERM is received. *)
	while !flag do
		 Lib.minisleep 0.5;				
		 let messages = Event.recv () in
     List.iter
	     (fun message -> 
         match message with
        
  		    (* Add invariant to the property list to verify when it's received. *)
          | (Event.Invariant (_, invar)) ->

					  flag := false;
	          if 
					    List.for_all 
	               (fun v -> 
							     (Numeral.to_int (Var.offset_of_state_var_instance v)) = 0) 
						     (TransSys.vars_of_term invar) 
					  then
						  (
	             (debug indtrace
                 "invariant_'0 invariant_property_%d = %a" !counter
                 Term.pp_print_term invar
                 end);
	              transSys.TransSys.props <- ("invariant_property_"^(string_of_int !counter), invar) :: transSys.TransSys.props;
						  )
	          
	          else
	           (
	             (debug indtrace
                 "invariant_'1 invariant_property_%d = %a" !counter
                 Term.pp_print_term invar
                 end);
							 premises_1 := invar :: !premises_1;
	             invariants_1 := ("invariant_property_"^(string_of_int !counter), invar) :: !invariants_1;
	           ); 
        
	          counter := !counter + 1;
       
        (* Irrelevant message received. *)
        | _ ->
					()
    
        ) messages;
	done;

  let prop_pairs = transSys.TransSys.props in

  let premises = List.append (List.map snd prop_pairs) !invs in

  (match prop_pairs with

    (* Terminate when there is nothing to check *)
    | [] -> Event.log `IND Event.L_error "No property to check"

    | _ -> init transSys prop_pairs premises !invariants_1 !premises_1);


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
