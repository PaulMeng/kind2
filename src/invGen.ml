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


(* Current step in BMC *)
let bmcK = ref Numeral.zero

(* Current step in IND *)
let indK = ref Numeral.zero

(* Current step in IND *)
let count = ref Numeral.zero

(* We don't need to clean up anything *)
let on_exit _ = ()

(* Hashtables for the implication graph*)

module THT = Term.TermHashtbl

(* Map of term representative to a term list it represents*)
let nodes_hashtl = Term.TermHashtbl.create 7
let new_nodes_hashtl = Term.TermHashtbl.create 7

(* Map of term representative to a list of representatives (implication)*)
let outgoing_hashtl = Term.TermHashtbl.create 7
let new_outgoing_hashtl = Term.TermHashtbl.create 7

let incoming_hashtl = Term.TermHashtbl.create 7
let new_incoming_hashtl = Term.TermHashtbl.create 7

(* Map of callee node and calling node *)
let node_calls_hashtl = UfSymbol.UfSymbolHashtbl.create 7

(**Merge term sets of the same type*)
let rec merge_in accum (t, s) = function

  | [] -> (t, s)::accum
  
  | (t', s')::tl -> 
    
    if Type.equal_types t t' then
      
      List.rev_append
        ((t, Term.TermSet.union s s')::tl)
        accum
        
    else
      
      merge_in ((t', s')::accum) (t, s) tl      

(* Make mode terms from mode variables*)
let rec make_mode_terms t ubound lbound acc =
  
  if Numeral.equal ubound lbound then
    
    Term.TermSet.add (Term.mk_eq [t; Term.mk_num ubound]) acc
    
  else
    
    make_mode_terms t ubound (Numeral.succ lbound) (Term.TermSet.add (Term.mk_eq [t; Term.mk_num lbound]) acc)
    
    
(* collect all subterms from a term*)
let rec collect_subterms uf_defs (fterm:Term.T.flat) (acc:((Type.t*Term.TermSet.t) list) list) : (Type.t*Term.TermSet.t) list =
  
  match fterm with
  
  | Term.T.App (s, l) as app ->
    
    let node_subterms = 
      
      (* Process UF symbol*)
      if Symbol.is_uf s then
        
        (
          
          try 
            
            (* Find the uf_def *)
            let uf_def = 
              
              List.find 
              
                (fun (symbol, t) ->
                  
                  symbol = Symbol.uf_of_symbol s)
                  
                uf_defs
                
            in
            
            (debug inv "calling subnode = %s " (UfSymbol.string_of_uf_symbol (fst uf_def)) end);
          
            (* Paire up variables and values *)
            let var_value_pair_list = 
              
              List.combine (fst (snd uf_def)) l
              
            in
            
            (* Make let bindings for the uninterpreted function*)
            let let_binding_uf_term = 
              
              Term.mk_let var_value_pair_list (snd (snd uf_def))
              
            in
            
            (* Recurse into the uninterpreted function to extract subterms*)
            extract_terms uf_defs let_binding_uf_term
            
          with Not_found -> failwith "uf_def not found!"
          
        )
      else
        (
           []
        )
        
    in  
      
    
    let t = Term.construct app in
    
    let t_type = Term.type_of_term t in
    
    let f_list = 
      
      if Flags.invgen_bool_complement () then
        
        (t_type, Term.TermSet.union (Term.TermSet.singleton t) (Term.TermSet.singleton (Term.negate t)))::(List.flatten acc)
        
      else 
        
        (t_type, Term.TermSet.singleton t)::(List.flatten acc)
        
    in
    
    List.fold_left
    
      (fun accum' (t, s) ->
        merge_in [] (t, s) accum')
        
    []
    (f_list@node_subterms)
                  
  | Term.T.Const c as f -> 
    
    (match acc with 
    
      | [] ->
        
        let t = Term.construct f in
        
        let t_type = Term.type_of_term t in
        
        (
          
         match Type.node_of_type t_type with
        
          | Type.IntRange (u, l) ->
            [(Type.t_int, Term.TermSet.singleton t)]
            
          | _ -> [(t_type, Term.TermSet.singleton t)]
          
        )       
      | _ -> assert false)
              
  | Term.T.Var v as variable -> 
    
    (match acc with
      | [] ->
       
        let t = Term.construct variable in
        
        let var_type = Term.type_of_term t in
        
        (
          match Type.node_of_type var_type with
          
          | Type.IntRange (u, l) ->
            if Flags.invgen_mode_invariant () then
              
              (
                let (ubound, lbound) =
                  Type.bounds_of_int_range (Term.type_of_term t) 
                in
                
                let mode_terms_set = 
                  make_mode_terms t ubound lbound Term.TermSet.empty
                in
                
                [(Type.t_int, Term.TermSet.singleton t); (Type.t_bool, mode_terms_set)]
              )
              
            else
              
              [(Type.t_int, Term.TermSet.singleton t)]
                  
          | Type.Bool when (Flags.invgen_bool_complement ())->
            
            [(var_type, Term.TermSet.union (Term.TermSet.singleton t) (Term.TermSet.singleton (Term.negate t)))]    
          
          | _ -> [(var_type, Term.TermSet.singleton t)]
        )
                    
      | _ -> assert false)
      
  | Term.T.Attr (t, _) -> List.flatten acc
    
(** Extract all subterms from a term *)  
and extract_terms uf_defs t =
  
  Term.eval_t (collect_subterms uf_defs) t
  

(** Extract canddiate terms from uf_defs*)
let extract_candidate_terms ts =
  
  let uf_defs = TransSys.uf_defs ts in
      
  (*Extract subterms for both init and trans state of a node*)    
  let term_sets_list =
    
    List.map
    
      (fun (init_pred, trans_pred) ->
        
        (fst init_pred, (extract_terms uf_defs (snd (snd init_pred))), 
        
          fst trans_pred, (extract_terms uf_defs (snd (snd trans_pred))))
        
      ) ts.TransSys.pred_defs 
  in
  
  List.map 
  
    (fun (init_pred_symbol, init_term_set_list, 
            trans_pred_symbol, trans_term_set_list) -> 
      
      (trans_pred_symbol,
      
       (List.map
      
        (fun (t, t_set)->
          
          let trans_t_term_set = 
            
            try
              
              (List.assoc t trans_term_set_list)
              
            with Not_found -> Term.TermSet.empty
              
          in
          
          (t, Term.TermSet.union t_set trans_t_term_set)
          
        ) init_term_set_list))
          
   ) term_sets_list


  
(* Safely add an edge to the edge hashtables*)  
let edge_hashtbl_safe_add ht (n_1:Term.t) (n_2:Term.t):unit = 
   
  if THT.mem ht n_1 then 
    (
      if (List.mem n_2 (THT.find ht n_1)) then
        ()
      else  
        THT.replace ht n_1 (n_2::(THT.find ht n_1))
    )
  else
    
    THT.add ht n_1 [n_2]
    
(* Safely remove an edge from the edge hashtables*)
let edge_hashtbl_safe_remove ht n_1 n_2 =  
  
  if THT.mem ht n_1 then
    
    (
      let new_value = 
        (List.filter (fun t -> t <> n_2) (THT.find ht n_1))
      in
      
      if new_value = [] then
        THT.remove ht n_1
      else 
        THT.replace ht n_1 new_value
    )

    
(*Add edges between the splited node and the destination nodes of the splited node's parent*)    
let add_new_outgoing_edges src new_node =
  
  if src = new_node then
    
    ()
    
  else
    (
      (*Retrieve all the parent's destination nodes*)
      let dest_nodes = THT.find outgoing_hashtl src in 
      
      if List.length dest_nodes <> 0 then
        (
          (*Add new_node as incoming node for the destination node*)
          List.iter
            (fun dest ->
              edge_hashtbl_safe_add incoming_hashtl dest new_node
              ) dest_nodes;
          
          (*Add the new outgoing edges*)
          THT.replace outgoing_hashtl new_node dest_nodes 
        )
    )


(* Remove useless (isolated or empty) nodes*)
let clean_graph _ =
  
  (*(debug inv "Cleaning up graph!!!!!!!!!!!!!!!!!!!" end);*)
  
  (*Clear the temporary incoming and outgoing hashtable*)
  THT.reset new_outgoing_hashtl;
  THT.reset new_incoming_hashtl;
  
  (*Reroute edges around nodes*)
  
  THT.iter
    (fun k v ->
      
      if v = [] then
        
        (
          (*Reroute edges around the empty node*)
          if ((THT.mem incoming_hashtl k) && (THT.mem outgoing_hashtl k)) then
            (
             
              List.iter 
              (fun incoming_node ->
                List.iter
                  (fun outgoing_node ->
                    (*(debug inv "incoming and empty node edge = %s ##### %s" (Term.string_of_term incoming_node) (Term.string_of_term k) end);*)
                    edge_hashtbl_safe_add outgoing_hashtl incoming_node outgoing_node;
                    edge_hashtbl_safe_add incoming_hashtl outgoing_node incoming_node;
                    edge_hashtbl_safe_remove incoming_hashtl outgoing_node k;
                    edge_hashtbl_safe_remove outgoing_hashtl incoming_node k;
                    
                  ) (THT.find outgoing_hashtl k) 
              ) (THT.find incoming_hashtl k);
              
            )
          (*Remove incoming edges to other nodes from this empty node*)
          else if THT.mem outgoing_hashtl k then
            (
              (*(debug inv "22222222222222222$$$$$$$$$$$$$$$$$$new node = %s and term list length = %d" (Term.string_of_term k) (List.length v) end);*)
              
              List.iter
                (fun outgoing_node ->
                
                  edge_hashtbl_safe_remove incoming_hashtl outgoing_node k;
                  
                ) (THT.find outgoing_hashtl k)               
              
            ) 
            
          (*Remove incoming edges to the empty node from other nodes*)  
          else if THT.mem incoming_hashtl k then
            (
             (* (debug inv "33333333333333333333$$$$$$$$$$$$$$$$$$ new node = %s and term list length = %d" (Term.string_of_term k) (List.length v) end);*)
              
              List.iter
                (fun incoming_node ->
                
                  edge_hashtbl_safe_remove outgoing_hashtl incoming_node k;
                  
                ) (THT.find incoming_hashtl k);
              
            );
            
          (*Remove all edges connected with empty node k*)
          THT.remove incoming_hashtl k;
          THT.remove outgoing_hashtl k  
        )
      ) new_nodes_hashtl;
      
  (*Remove empty nodes*)    
  THT.iter
    (fun rep term_list ->
      if term_list = [] then
        
        THT.remove nodes_hashtl rep
      
      ) new_nodes_hashtl;
  
  THT.reset new_nodes_hashtl;

  (*Remove nodes of size less than 2 and does not have imcoming or outgoing edges*)
  THT.iter
    (fun r term_list ->
      if ((List.length term_list) < 2 
         &&
         (not (THT.mem outgoing_hashtl r))
         &&
         (not (THT.mem incoming_hashtl r)))
        then
          THT.remove nodes_hashtl r
    )
  nodes_hashtl

(* Update the graph based on the splits and old graph*)
let update_graph chains =
  
  let new_edges = 
    
    THT.iter
    
      (fun src dest ->
        
        List.iter
        
          (fun dest' ->
            
            (*(debug inv "key = %s " (Term.string_of_term src) end);*)
            
            let source_chain = 
            
              try 
              
                List.assoc src chains 
              
              with Not_found -> raise Not_found
            
            in
            
            let destination_chain = 
              
              try 
                
                List.assoc dest' chains
              
              with Not_found -> raise Not_found
            
            in
            
            edge_hashtbl_safe_add new_outgoing_hashtl (fst (fst source_chain)) (fst (fst destination_chain));
            edge_hashtbl_safe_add new_incoming_hashtl (fst (fst destination_chain)) (fst (fst source_chain));
            
            edge_hashtbl_safe_add new_outgoing_hashtl (fst (snd source_chain)) (fst (snd destination_chain));
            edge_hashtbl_safe_add new_incoming_hashtl (fst (snd destination_chain)) (fst (snd source_chain));
        
            if (snd (fst source_chain)) = [] && (snd (snd destination_chain)) = [] then
              (
                
                (*(debug inv "src0 -> dest1 edge: %s ----->  %s" (Term.string_of_term (fst (fst source_chain))) (Term.string_of_term (fst (snd destination_chain))) end);*)
                 (*((fst source_chain, snd destination_chain)::(fst source_chain, fst destination_chain)::(snd source_chain, snd destination_chain)::edges')*)
                edge_hashtbl_safe_add new_outgoing_hashtl (fst (fst source_chain)) (fst (snd destination_chain));
                edge_hashtbl_safe_add new_incoming_hashtl (fst (snd destination_chain)) (fst (fst source_chain));
                
              );
              
           (* else
            
              ((fst source_chain, fst destination_chain)::(snd source_chain, snd destination_chain)::edges')*)

            
          ) dest    
          
      ) outgoing_hashtl
  in
  (*
  List.iter
    (fun (s, d) ->
      
      edge_hashtbl_safe_add outgoing_hashtl (fst s) (fst d);
      edge_hashtbl_safe_add incoming_hashtl (fst d) (fst s);
          
    ) (new_edges:((Term.t*(Term.t list))*(Term.t*(Term.t list))) list);*)
  
  THT.reset outgoing_hashtl;
  THT.reset incoming_hashtl; 
  THT.reset nodes_hashtl;
  
  (* Add the new generated outgoing edges into the outgoing edges hash tables*)
  THT.iter
    ( fun src dest ->
    
      THT.add outgoing_hashtl src dest
      
    ) new_outgoing_hashtl;   
  
  (* Add the new generated incoming edges into the edges hash tables*)
  THT.iter
    ( fun src dest ->
      
      THT.add incoming_hashtl src dest
      
    ) new_incoming_hashtl;
  
  (* Add the new generated nodes into the nodes hash tables*)
  THT.iter
  
    ( fun rep term_list ->
      
      THT.add nodes_hashtl rep term_list
      
      ) new_nodes_hashtl 

    

(** Split nodes based on the model*)
let rebuild_graph uf_defs model k =
  
  (* Split nodes into chains*)
  let chains = 
    
    THT.fold
    
      (fun rep term_list init ->
      
        let (t_list_1, t_list_0) =
          
          List.partition
            (fun t ->
             (* (debug inv "repo term = %s " (Term.string_of_term t) end);*)
              Eval.bool_of_value
                (Eval.eval_term uf_defs model (Term.bump_state k t))
            ) term_list
            
        in
        
        (*(debug inv "2 chains: List1.length= %d ; List0.length= %d"(List.length t_list_1) (List.length t_list_0) end);
        
        (debug inv "3 rep = %s" (Term.string_of_term rep) end);*)
        
        if (List.length t_list_0) <> 0 && (List.length t_list_1) <> 0 then
          
          (
            
            (*New representative terms for the new nodes*)
            let rep_0 = List.hd t_list_0 in
            let rep_1 = List.hd t_list_1 in
            
            (*Add new outgoing and incoming edges based on the previous implication graph*)
            (*add_new_outgoing_edges rep rep_0;
            add_new_outgoing_edges rep rep_1;
            add_new_incoming_edges rep rep_0;
            add_new_outgoing_edges rep rep_1;*)
            
            (*Add the edges from 0 node to 1 node*)
            edge_hashtbl_safe_add new_outgoing_hashtl rep_0 rep_1;
            edge_hashtbl_safe_add new_incoming_hashtl rep_1 rep_0;
            
            (*Store the new nodes*)
            THT.replace new_nodes_hashtl rep_0 t_list_0;
            THT.replace new_nodes_hashtl rep_1 t_list_1;

            (rep, ((rep_1, t_list_1), (rep_0, t_list_0)))::init
            
          )
          
        else if (List.length t_list_0 <> 0) then
          
          (
            
            let unique_term_rep = snd (Term.mk_named Term.t_true) in
            
            THT.replace new_nodes_hashtl (List.hd t_list_0) t_list_0;
            THT.replace new_nodes_hashtl unique_term_rep t_list_1;
            
            (rep, ((unique_term_rep, t_list_1), (List.hd t_list_0, t_list_0)))::init
          
          )
          
        else
          
          (
            
            let unique_term_rep = snd (Term.mk_named Term.t_false) in
            THT.replace new_nodes_hashtl (List.hd t_list_1) t_list_1;
            THT.replace new_nodes_hashtl unique_term_rep t_list_0;
            
            (rep, ((List.hd t_list_1, t_list_1), (unique_term_rep, t_list_0)))::init
          
          )
          
      ) nodes_hashtl []
  in
  
  (*Update the graph based on chains*)
  update_graph chains;
  
  clean_graph ()

(* Make candidate invariants out of the graph*)
let mk_candidate_invariants () = 
  
  (*(debug inv "1 Inside mk_candidate_invariants" end);*)
  
  (*Make candidate invariants out of nodes*)
  let candidate_invariants =
    
    THT.fold
    
      (fun rep term_list accum ->
        
        let term_list' = 
          List.filter (fun x -> (not (Term.equal x rep))) term_list
        in
        
        (List.map
          (fun t ->
            count := Numeral.succ !count;
            ("inv_"^(Numeral.string_of_numeral !count), Term.mk_eq [rep; t])
         ) term_list')@accum
        
     ) nodes_hashtl []
    
  in
  
  (debug inv "################Number of Nodes = %d" (THT.length nodes_hashtl) end);
  
  (*Make candidate invariants out of edges*)
  let candidate_invariants' =
    
    THT.fold
    
      (fun source destination_list accum ->
        
        (List.map
          (fun t ->
            
            count := Numeral.succ !count;
            
            let inv = Term.mk_implies [source; t] in
            
            ("inv_"^(Numeral.string_of_numeral !count), inv))
            
        destination_list)@accum)
        
    outgoing_hashtl []
  in

  List.rev_append candidate_invariants candidate_invariants'

(* Compute the difference of two lists*)
let list_difference l_1 l_2 = 
  
  let l_2' = List.map (fun (n, t) -> t) l_2 in
  
  List.fold_left
    (fun acc (name, inv) ->
      if (List.mem inv l_2') then
        acc
      else
        (name, inv)::acc
      ) [] l_1
  

(*Call BMC to create stable implication graph*)
let rec create_stable_graph solver ts k candidate_invs refined =
  
  (* Call BMC until no properties disproved at current step*)
  let props_unknown, props_invalid, model = 
    
    Bmc.bmc_invgen_step false solver ts k candidate_invs
    
  in
  
  
  (*Record current bmc step*)
  bmcK := k;
  (debug inv " BMC k = %d" (Numeral.to_int k) end);
  
  (*
  List.iter
  (fun (cex,prop) ->
    
    List.iter 
      (fun (name, p) -> 
        (debug inv "props_invalid  = %s" (Term.string_of_term p) end);
      ) prop
    
    ) props_invalid;*)
  
  (*rebuild the graph if some candidate invariants are disproved by BMC*)
  if List.length props_invalid <> 0 then
    (
      let uf_defs = TransSys.uf_defs ts in
    
      rebuild_graph uf_defs model k;
        
      create_stable_graph solver ts k (mk_candidate_invariants ()) false
    )
  else
    (
      
      if not refined then
        create_stable_graph solver ts (Numeral.succ k) (mk_candidate_invariants ()) true
      
    )

(* Add "TRUE" "FALSE" terms to the boolean candidate terms list*)    
let add_true_false_terms bool_terms =
  if
    not 
    ((Term.TermSet.mem Term.t_true bool_terms) || (Term.TermSet.mem Term.t_false bool_terms)) 
  then
    Term.TermSet.add Term.t_false (Term.TermSet.add Term.t_true bool_terms)
  else if not (Term.TermSet.mem Term.t_true bool_terms) then
    Term.TermSet.add Term.t_true bool_terms
  else if not (Term.TermSet.mem Term.t_false bool_terms) then
    Term.TermSet.add Term.t_false bool_terms
  else 
    bool_terms
    
(*Remove trivial invariants such as "true", "false -> bla", "a = a" and etc*)
let remove_trivial_invariants invariants =
   
  List.filter
    (fun (name, inv) ->
      
      not
      (
        Term.node_symbol_of_term inv == Symbol.s_implies
        &&
        Term.equal Term.t_false (List.hd (Term.node_args_of_term inv))
        &&
        Term.vars_of_term inv = Var.VarSet.empty
      )

    ) invariants

let rec produce_invariants bmc_solver ind_solver ts ind_k invariants = 
  
  (debug inv " after creating stable graph candidate_invariants length = %d" (List.length (mk_candidate_invariants ())) end);
  
  let candidate_invariants = 
    (list_difference (mk_candidate_invariants ()) invariants)
  in
  
  match candidate_invariants with
  | [] -> (debug inv "No more candiate invariants!" end);
  
  | _ ->
    (
      let props_k_ind, props_not_k_ind = 
        
        IndStep.ind_step 
          ind_solver 
          ts 
          [] 
          candidate_invariants
          ind_k
        
      in
      (debug inv "ind_k = %d" (Numeral.to_int ind_k) end);
      (debug inv "bmc_k = %d" (Numeral.to_int !bmcK) end);
      (*Send out invariants props_k_ind*)
      if (List.length props_k_ind) <> 0 && (Numeral.leq ind_k !bmcK) then
        (
          (*Remove trivial invariants*)
          (*Send out invariants*)
          List.iter
            (fun (name, term) -> 
              (debug inv "  invariant = %s" (Term.string_of_term term) end);
              Event.invariant term
            ) (remove_trivial_invariants props_k_ind); 
          
        );
      
      if ((List.length props_not_k_ind) <> 0 && (Numeral.gt ind_k !bmcK) ) then
        
        ( 
          create_stable_graph 
            bmc_solver 
            ts 
            (Numeral.succ !bmcK) 
            (list_difference (mk_candidate_invariants ()) invariants)
            false
        );
        
      produce_invariants bmc_solver ind_solver ts  (Numeral.succ ind_k) (List.rev_append invariants props_k_ind) 
      
    )
  

(* Generate invariants from candidate terms*)
let inv_gen trans_sys = 
  
  (*Extract candidate terms from transition system*)
  let candidate_terms = extract_candidate_terms trans_sys in
  
  let bool_terms =
    
    List.fold_left
    
      (fun accum (trans_symbol, terms_list) ->
        
        (trans_symbol, add_true_false_terms (List.assoc Type.t_bool terms_list))::accum
        
      )
      
    [] candidate_terms
    
  in
  
  List.iter
    (fun (trans_s, t) ->
     
      (debug inv "Extract symbol trans = %s " (UfSymbol.string_of_uf_symbol trans_s) end);
      
      List.iter
        (fun (x, y) ->
          (debug inv "  Type = %s" (Type.string_of_type x) end); 
          Term.TermSet.iter
            (fun z ->
              (debug inv "Term = %s" (Term.string_of_term z) end);
            ) y
       ) t
  ) candidate_terms;
  
  
  let uf_defs = TransSys.uf_defs trans_sys in
  
  let ufsymbol_var_list =
    
    List.map
      ( fun (s, v_t) ->
          List.map 
            (fun var ->
              StateVar.uf_symbol_of_state_var (Var.state_var_of_state_var_instance var)
            ) (fst v_t)
             
      ) uf_defs
  in
    
    
  let ufsymbol_set = 
    List.fold_left
      ( fun empty_set elt ->
          UfSymbol.UfSymbolSet.add 
            elt
            empty_set
        )
      UfSymbol.UfSymbolSet.empty (List.flatten ufsymbol_var_list)
  in
 
  
  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic trans_sys in
  
  (* Create BMC solver instance *)
  let bmc_solver = 
    Bmc.S.new_solver ~produce_assignments:true logic 
  in
  
  (* Declare uninterpreted function symbols *)
  TransSys.iter_state_var_declarations
    trans_sys
    (Bmc.S.declare_fun bmc_solver);
  
  
  UfSymbol.UfSymbolSet.iter
    ( fun ufsymbol ->
       Bmc.S.declare_fun bmc_solver ufsymbol
      ) ufsymbol_set;
    
  
  (* Define functions *)
  TransSys.iter_uf_definitions
    trans_sys
    (Bmc.S.define_fun bmc_solver);

  (* Assert initial state constraint *)
  Bmc.S.assert_term bmc_solver (TransSys.init_of_bound trans_sys Numeral.zero);
  
  (* Create IND solver instance *)
  let ind_solver = 
    IndStep.S.new_solver ~produce_assignments:true logic 
  in
  
  (* Declare uninterpreted function symbols *)
  TransSys.iter_state_var_declarations
    trans_sys
    (IndStep.S.declare_fun ind_solver);
    
  UfSymbol.UfSymbolSet.iter
    ( fun ufsymbol ->
       IndStep.S.declare_fun ind_solver ufsymbol
      ) ufsymbol_set;
  
  (* Define functions *)
  TransSys.iter_uf_definitions
    trans_sys
    (IndStep.S.define_fun ind_solver);

  (* Assert invariants C[x_0] 

     Asserted before push, will be preserved after restart *)
  IndStep.S.assert_term
    ind_solver
    (TransSys.invars_of_bound trans_sys Numeral.zero);

  (* New context for assertions to be removed on restart *)
  IndStep.S.push ind_solver;
    
  if (List.length bool_terms) <> 0 then
    
    (
      List.iter
        (fun (_, terms_set) ->
          
          if not (Term.TermSet.is_empty terms_set) then
            
            let terms_list = Term.TermSet.elements terms_set in
            
            THT.add nodes_hashtl (List.hd (terms_list)) terms_list;
            
        ) bool_terms;
      
      
      (*Create a stable implication graph by BMC*)
      create_stable_graph bmc_solver trans_sys Numeral.zero (mk_candidate_invariants ()) false;
      
      produce_invariants bmc_solver ind_solver trans_sys Numeral.zero []
      
    )
  else
    (debug inv "No boolean candidate terms proposed!" end)

(* Entry point *)
let main trans_sys = 
  
  Event.set_module `INVGEN;
  
  inv_gen trans_sys


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
