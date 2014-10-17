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


(* Output statistics *)
let print_stats () = 

  Event.stat 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.invgen_stats_title, Stat.invgen_stats;
     Stat.smt_stats_title, Stat.smt_stats]


(* Print stats *)
let on_exit _ = 
  
  (* Stop all timers *)
  Stat.invgen_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  print_stats ()

(* Hashtables for the implication graph*)

module THT = Term.TermHashtbl
module UHT = UfSymbol.UfSymbolHashtbl
module TTS = Term.TermSet

let eliminate_term = ref true

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

(* Map of a node rep and its trans_symbol in the implication graph*)
let node_symbol_hashtl = Term.TermHashtbl.create 7

(**Merge term sets of the same type*)
let rec merge_in accum (t, s) target = 
  
  match target with

  | [] -> (t, s)::accum
  
  | (t', s')::tl -> 
    
    if Type.equal_types t t' then
      
      List.rev_append
        ((t, TTS.union s s')::tl)
        accum
        
    else
      
      merge_in ((t', s')::accum) (t, s) tl    


(* Make mode terms from mode variables*)
let rec make_mode_var_equations t ubound lbound acc =
  
  if Numeral.equal ubound lbound then
    
    TTS.add (Term.mk_eq [t; Term.mk_num ubound]) acc
    
  else
    
    make_mode_var_equations t ubound (Numeral.succ lbound) (TTS.add (Term.mk_eq [t; Term.mk_num lbound]) acc)
    
    
(* collect all subterms from a term*)
let rec collect_subterms ts calling_node_symbol (fterm:Term.T.flat) (acc:((Type.t*TTS.t) list) list) : (Type.t*TTS.t) list =
  
  match fterm with
  
  | Term.T.App (s, l) as app ->
     
    let node_subterms = 
      
      (* Process UF symbol*)
      if Symbol.is_uf s then
        
        (

          let uf_defs = TransSys.uf_defs ts in
          
          let uf_symbol_of_term_symbol = Symbol.uf_of_symbol s in
          
          (* Find the uf_def *)
          let (_, (uf_vars, uf_term)) = 
            
            try 
                
              List.find 
              
                (fun (symbol, t) ->
                  
                  UfSymbol.equal_uf_symbols symbol uf_symbol_of_term_symbol)
                  
                uf_defs
                
             with Not_found -> failwith "uf_def not found!"
          
            in
        
          
         (* (debug inv "calling subnode = %s " (UfSymbol.string_of_uf_symbol (fst uf_def)) end);*)
          
          (* Paire up variables and values *)
          let var_value_pair_list = 
            
            List.combine uf_vars l
            
          in
          
          (* Add only the transition state of callee and calling nodes to the hashtable*)
          if TransSys.is_trans_uf_def ts uf_symbol_of_term_symbol then
            
            (
              UHT.add node_calls_hashtl uf_symbol_of_term_symbol (calling_node_symbol, var_value_pair_list)
            );            
          
          (* Make let bindings for the uninterpreted function*)
          let let_binding_uf_term = 
            
            Term.mk_let var_value_pair_list uf_term
            
          in
          
          (* Recurse into the uninterpreted function to extract subterms*)
          extract_terms ts uf_symbol_of_term_symbol let_binding_uf_term
                                          
        )
      else
        (
           []
        )
        
    in  

    let t = Term.construct app in        
    let t_type = Term.type_of_term t in
    
    let f_list = 
      
      if (Type.equal_types t_type Type.t_bool) && Flags.invgen_bool_complement () then
        (
         
          (t_type, TTS.add t (TTS.singleton (Term.negate t)))::(List.flatten acc)
        )
        
      else 
        (          
          (t_type, TTS.singleton t)::(List.flatten acc)
        )
        
    in
    
    List.fold_left
    
      (fun accum' (t, s) ->
        
        merge_in [] (t, s) accum'
        
      ) 
      []
      (f_list @ node_subterms)
                  
  | Term.T.Const c as f -> 

    (match acc with 
    
      | [] ->
        
        let t = Term.construct f in
                
        let t_type = Term.type_of_term t in
        
        (
          
         match Type.node_of_type t_type with
        
          | Type.IntRange (u, l) ->
            
            [(Type.t_int, TTS.singleton t)]
            
          | _ -> [(t_type, TTS.singleton t)]
          
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
                  make_mode_var_equations t ubound lbound TTS.empty
                in
                
                [(Type.t_int, TTS.singleton t); (Type.t_bool, mode_terms_set)]
              )
              
            else
              
              [(Type.t_int, TTS.singleton t)]
                  
          | Type.Bool when (Flags.invgen_bool_complement ())->                        
            
            [(var_type, TTS.add t (TTS.singleton (Term.negate t)))]    
          
          | _ -> [(var_type, TTS.singleton t)]
        )
                    
      | _ -> assert false)
      
  | Term.T.Attr (t, _) -> List.flatten acc
    
(** Extract all subterms from a term *)  
and extract_terms ts calling_node_symbol t =
  
  Term.eval_t (collect_subterms ts calling_node_symbol) t   

(*Convert a term list to a term set*)  
let rec termset_of_list = function
  | [] -> TTS.empty
  | hd::tl -> TTS.add hd (termset_of_list tl)

(** Extract canddiate terms from uf_defs*)
let extract_candidate_terms ts =
      
  (*Extract subterms for both init and trans state of a node*)    
  let term_sets_list =
    
    List.map
    
      (fun (init_pred, trans_pred) ->
        
        (*Decompose the AND term into small ones and extract both sides of equation terms*)
        let init_def = snd (snd init_pred) in
        
        let trans_def = snd (snd trans_pred) in

        let decomposed_init_trans_pred = 
          
          TTS.union
          
          (
            
            let flat_term = Term.destruct init_def in
            
            match flat_term with

            | Term.T.App (s, l) when (Symbol.equal_symbols s Symbol.s_and) ->
              
              termset_of_list l 
              
            | _ -> TTS.singleton init_def
          )
          (
                                  
            let flat_term = Term.destruct (Term.bump_state (Numeral.of_int (-1)) trans_def) in
            
            match flat_term with

            | Term.T.App (s, l) when (Symbol.equal_symbols s Symbol.s_and) ->
              
              termset_of_list l 
              
            | _ -> TTS.singleton trans_def
          )
            
        in
        
        (* Break the equation terms of init and trans defs*)
        let init_trans_terms_set = 
          
          TTS.fold 
          
            (fun term term_set ->
              
              let flat_term = Term.destruct term in
              
              match flat_term with

              (*Break the equation and add the both sides' terms into term set*)
              | Term.T.App (s, l) when (Symbol.equal_symbols s Symbol.s_eq) ->

                List.fold_left
                  (fun accum elt->
                    TTS.add elt accum
                  )
                  term_set
                  l
                                                     
              | _ -> TTS.add term term_set 
              
            ) 
            decomposed_init_trans_pred
            TTS.empty
          
        in
          
        let extracted_init_trans_terms_set = 
          
          TTS.fold
            (
              fun term terms_set_list ->
                
                let subterms = 
                  extract_terms ts (fst trans_pred) term in
                
                List.fold_left
                  (fun accum (t, s) ->
                     merge_in [] (t, s) accum
                  )
                  terms_set_list
                  subterms                  
              
            )
            init_trans_terms_set
            []
        in

        (fst trans_pred, extracted_init_trans_terms_set)
        
      ) (TransSys.uf_defs_pairs ts)
  in
  
  term_sets_list


(*Pick an initial representative for equivalence class *)
(*other than true or false term to avoid conflict*)
let rec pick_rep_term term_list =
  
  match term_list with

  | [] -> assert false
  | hd::tl -> 
    
    if not ((Term.equal hd Term.t_true) || (Term.equal hd Term.t_false)) then
      hd
    else if tl = [] then      
      snd (Term.mk_named hd)
    else
      pick_rep_term tl
  
(* Safely add an edge to the edge hashtables*)  
let edge_hashtbl_safe_add ht (n_1:Term.t) (n_2:Term.t):unit = 
  try 
    let node_list = THT.find ht n_1 in 
    
    if List.mem n_2 node_list then 
      ()
    else 
      THT.replace ht n_1 (n_2::(THT.find ht n_1))

  with Not_found ->
    
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

(* Remove useless (isolated or empty) nodes*)
let clean_graph _ =
    
  (*Clear the temporary incoming and outgoing hashtable*)
  THT.reset new_outgoing_hashtl;
  THT.reset new_incoming_hashtl;
  
  (*Reroute edges around nodes*)
  
  THT.iter
    (fun k v ->
      
      if v = [] then
        
        (
                    
          (*Reroute edges around the empty node; i.e n1->n2->n3; if n2_1 is empty, *)
          (* need to add edge between the incoming nodes to n2_1 and outgoing nodes from n2_1*)
          if ((THT.mem incoming_hashtl k) && (THT.mem outgoing_hashtl k)) then
            (
             
              List.iter 
              (fun incoming_node ->
                  assert (not (Term.equal incoming_node k));
                 (*(debug inv "incoming and empty node edge = %s #####" (Term.string_of_term incoming_node) end);*)
                List.iter
                  (fun outgoing_node ->
                    (*(debug inv "incoming and empty node edge = %s ##### %s" (Term.string_of_term incoming_node) (Term.string_of_term k) end);*)
                    edge_hashtbl_safe_add outgoing_hashtl incoming_node outgoing_node;
                    edge_hashtbl_safe_add incoming_hashtl outgoing_node incoming_node;
                    edge_hashtbl_safe_remove incoming_hashtl outgoing_node k;
                    edge_hashtbl_safe_remove outgoing_hashtl incoming_node k;
                    
                  ) 
                  (THT.find outgoing_hashtl k) 
              ) 
              (THT.find incoming_hashtl k);
              
            )
          (*Remove incoming edges to other nodes from this empty node if it does not have incoming edges*)
          else if THT.mem outgoing_hashtl k then
            (
              
              List.iter
                (fun outgoing_node ->
                
                  edge_hashtbl_safe_remove incoming_hashtl outgoing_node k;
                  
                ) (THT.find outgoing_hashtl k)               
              
            ) 
            
          (*Remove incoming edges to the empty node from other nodes if it does not have outgoing edges*)  
          else if THT.mem incoming_hashtl k then
            (
              
              List.iter
                (fun incoming_node ->
                
                  edge_hashtbl_safe_remove outgoing_hashtl incoming_node k;
                  
                ) (THT.find incoming_hashtl k);
              
            );
            
          (*Remove all edges connected with empty node k*)
          THT.remove incoming_hashtl k;
          THT.remove outgoing_hashtl k  
        )
      ) 
      new_nodes_hashtl;
      
  (*Remove empty nodes*)    
  THT.iter
    (fun rep term_list ->
      if term_list = [] then
        
        THT.remove nodes_hashtl rep
      
    )
    new_nodes_hashtl;
  
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
            
            let ((src_rep_1, src_list_1), (src_rep_0, src_list_0)) = 
            
              try 
              
                List.assoc src chains 
              
              with Not_found -> assert false
            
            in
            
            let ((dest_rep_1, dest_list_1), (dest_rep_0, dest_list_0)) = 
              
              try 
                
                List.assoc dest' chains
              
              with Not_found -> assert false
            
            in                       
           
            (*For edge n0->n1 in the old graph, we add new edge between their splited nodes*)
            (* n0_0->n1_0 and n0_1-> n1_1*)
            (*assert (not (Term.equal src_rep_1 dest_rep_1));
            assert (not (Term.equal dest_rep_1 src_rep_1));
            assert (not (Term.equal src_rep_0 dest_rep_0));
            assert (not (Term.equal dest_rep_0 src_rep_0));*)
            edge_hashtbl_safe_add new_outgoing_hashtl src_rep_1 dest_rep_1;
            edge_hashtbl_safe_add new_incoming_hashtl dest_rep_1 src_rep_1;
            
            edge_hashtbl_safe_add new_outgoing_hashtl src_rep_0 dest_rep_0;
            edge_hashtbl_safe_add new_incoming_hashtl dest_rep_0 src_rep_0;
            
            (*If n0_1 and n1_0 are empty, add an edge of n0_0 -> n1_1*)
            if src_list_1 = [] && dest_list_0 = [] then
              (
                assert (not (Term.equal src_rep_0 dest_rep_1));
                assert (not (Term.equal dest_rep_1 src_rep_0));                
                edge_hashtbl_safe_add new_outgoing_hashtl src_rep_0 dest_rep_1;
                edge_hashtbl_safe_add new_incoming_hashtl dest_rep_1 src_rep_0;
                
              );
            
          ) 
          dest    
          
      ) 
      outgoing_hashtl
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
    
      (fun rep term_list accum ->
        
       (*(debug inv "################## model ##################" end);
        List.iter
          (fun (var, value) ->
            
            (debug inv "%s = %s" (Var.string_of_var var) (Term.string_of_term value) end);
          )
          model;
          
        (debug inv "################## model ##################" end);    *)
                                 
        
        (*Split a node into two nodes based on their values*)  
        let (t_list_1, t_list_0) =          
            
            List.partition
              (fun t ->
                  (*(debug inv "--------- rep term = %s " (Term.string_of_term t) end);*)
                Eval.bool_of_value
                  (Eval.eval_term uf_defs model t)
              ) 
              term_list
            
          in 
                 
          match (t_list_0, t_list_1) with
          
          | ([], []) -> assert false
          
          | ([], _) -> 
            
            let unique_term_rep = snd (Term.mk_named Term.t_false) in
            let rep_1 = pick_rep_term t_list_1 in
            
            THT.replace new_nodes_hashtl rep_1 t_list_1;
            THT.replace new_nodes_hashtl unique_term_rep t_list_0;
                      
            (rep, ((rep_1, t_list_1), (unique_term_rep, t_list_0)))::accum
            
          | (_, []) ->
            
            let unique_term_rep = snd (Term.mk_named Term.t_true) in
            let rep_0 = pick_rep_term t_list_0 in
            
            THT.replace new_nodes_hashtl rep_0 t_list_0;
            THT.replace new_nodes_hashtl unique_term_rep t_list_1;        
            
            (rep, ((unique_term_rep, t_list_1), (rep_0, t_list_0)))::accum
            
          | (_, _) ->
            
            let rep_0 = pick_rep_term t_list_0 in
            let rep_1 = pick_rep_term t_list_1 in
            
            assert (not (Term.equal rep_0 rep_1));
            
            (*Add the edges from 0 node to 1 node*)
            edge_hashtbl_safe_add new_outgoing_hashtl rep_0 rep_1;
            edge_hashtbl_safe_add new_incoming_hashtl rep_1 rep_0;
            
            (*Store the new nodes*)
            THT.replace new_nodes_hashtl rep_0 t_list_0;
            THT.replace new_nodes_hashtl rep_1 t_list_1;                   
  
            (rep, ((rep_1, t_list_1), (rep_0, t_list_0)))::accum
          
      ) nodes_hashtl []
  in
  
  (*Update the graph based on chains*)
  update_graph chains;
  
  clean_graph ()


(*Is the candidate term already a known invariants*)
let is_invariant invariants term =
  (List.exists 
    (fun t -> 
      Term.equal term t) 
    invariants)

(* Make candidate invariants out of the graph*)
let mk_candidate_invariants invariants k =  
  
  (*Make candidate invariants from nodes*)
  let candidate_invariants =
    
    THT.fold
    
      (fun rep term_list accum ->              
        (List.fold_left
          (fun accum' t ->
            
            if Term.equal rep t then
              
              accum'
              
            else
              
              (
              
                (*Remove the name of a named term*)
                let rep' = 
                  if Term.is_named rep then Term.term_of_named rep else rep 
                in
                
                let eq_term = Term.mk_eq [rep'; t] in
                
                if not (is_invariant invariants eq_term) then
                  (
                    eq_term::accum'
                  )                     
                    
                else 
                  
                  accum'
              )
           ) 
          accum 
          term_list)
        
     ) 
    nodes_hashtl 
    []
    
  in
    
  (*Make candidate invariants from edges*)
  let candidate_invariants' =
    
    THT.fold
    
      (fun source destination_list accum ->
        
        (List.fold_left
          (fun accum' t ->
            
            (*Restore a named term*)
            let source' = if Term.is_named source then Term.term_of_named source else source in
            let t' = if Term.is_named t then Term.term_of_named t else t in
            let impl_term = Term.mk_implies [source'; t'] in
              
            (*(debug inv "*****  edge candidate invariant = %s" (Term.string_of_term inv') end);*)
            if not (is_invariant invariants impl_term) then
              (    
                impl_term::accum'
              ) 
              
            else 
              
              accum'
            )
            
          accum
          destination_list)
        )
        outgoing_hashtl 
        candidate_invariants
  in    

  candidate_invariants'

(* Compute the difference of two lists*)
let subtract_list l_1 l_2 = 
  
  let l_2' = List.map (fun (n, t) -> t) l_2 in
  
  List.fold_left
    (fun acc (name, inv) ->
      if (List.mem inv l_2') then
        acc
      else
        (name, inv)::acc
      ) [] l_1

(* Add "TRUE" "FALSE" terms to the boolean candidate terms list*)    
let add_true_false_terms bool_terms_list =
  
  let t_list = 
    
    if not (List.mem Term.t_true bool_terms_list) then
      
      Term.t_true::bool_terms_list
      
    else 
      
      bool_terms_list
  in
  
  if not (List.mem Term.t_false bool_terms_list) then
    
    Term.t_false::t_list
    
  else 
    
    t_list

    
(*Remove trivial invariants such as "true","bla -> true", "false -> bla", "a = a", no vars term and etc*)
let remove_trivial_invariants invariants =

  List.filter
    (fun inv ->
      
      not
      (        
        (Term.node_symbol_of_term inv == Symbol.s_implies
        &&
        (Term.equal Term.t_false (List.hd (Term.node_args_of_term inv))
         ||
         Term.equal Term.t_true (List.nth (Term.node_args_of_term inv) 1)
        )
        )      
      ||
        (Term.vars_of_term inv = Var.VarSet.empty)
      ||
        (Term.node_symbol_of_term inv == Symbol.s_eq
        &&
        (let args = Term.node_args_of_term inv in
         Term.equal (List.nth args 0)  (List.nth args 1)))
      
      )

    ) invariants

(* Instantiate subnode invariants up to the top node*)
let rec instantiate_invariant_upto_top_node paired_up_invariants accum ts =
  
  match paired_up_invariants with
  
  (*accum is a pair of two list; The first list contains all the top nodes invariants*)
  (* The second list contains non-top node invariants*)
  | [] -> accum

  | (symbol, term)::tl -> 
    
    (
      
      (*Find all its calling nodes for "symbol"*)
      let calling_node_list = 
        
        try 
      
          UHT.find_all node_calls_hashtl symbol 
      
        with Not_found -> []
      
      in
      
      (*Instantiate one level up *)
      let paired_up_invariants' = 
        
        List.map        
          (fun (calling_symbol, var_value_list) ->                      
            (*(debug inv "calling node symbol = %s for term = %s" (UfSymbol.string_of_uf_symbol calling_symbol) (Term.string_of_term term) end);*)
            let let_binding_term =               
              Term.mk_let var_value_list term
            
            in
            
            (calling_symbol, let_binding_term)
            
          ) 
          calling_node_list
      in
      
      let accum' = 
        (*Check if reaching the very top node*)
        match calling_node_list with

        | [] -> 
          
          (
            let trans_top = TransSys.trans_top ts             
            in
            
            (*Compare with top node symbol*)
            if UfSymbol.equal_uf_symbols (fst trans_top) symbol then
              
              let var_value_list = snd trans_top in              
              let top_invariant =                 
                Term.mk_let var_value_list term
              
              in
              
              (*Add the top invariant to the first list*)
              (top_invariant::(fst accum), snd accum)
            
            else
              (*Add the non-top invariant to the second list*)
              (fst accum, term::(snd accum))            
          )

        | _ -> (fst accum, term::(snd accum))

      in
      
      (*Check again for the rest of the invariants*)
      instantiate_invariant_upto_top_node 
        (paired_up_invariants'@tl) 
        accum'
        ts
    )
    

(* Instantiate invariants upto top node and send out them*)
let send_out_invariants lock_step_solver ts all_candidate_terms invariants =
  
  (* Pair up invariant with its node trans symbol*)
  let paired_up_invariants =
            
    List.fold_left            
      (fun accum term ->
                
        let var =
          List.hd (Var.VarSet.elements (Term.vars_of_term term)) 
                    
        in
        
        (*(debug inv "term = %s" (Term.string_of_term term) end);*)
        
        (*Find the term's node symbol from all candidate term list and pair up with it*)          
        let (node_symbol, _) = 
                  
          try
            
            List.find
              (fun (symbol, type_term_list) ->
                List.exists
                  (fun (_, term_set) ->
                    TTS.mem (Term.mk_var var) term_set
                   ) 
                   type_term_list
                          
               )
               all_candidate_terms
                      
          with Not_found -> assert false
        
        in 
        
        (node_symbol, term)::accum
                
       )
       []
       invariants
              
    in 
    
    (* Instantiate subnodes' invariants upto the very top node*)
    let top_node_invariants_list, subnode_invariant_list = 
      
      instantiate_invariant_upto_top_node paired_up_invariants ([], []) ts
      
    in
    
    (*Use subnodes invariants for invariant generation*)
    LockStepDriver.new_invariants lock_step_solver subnode_invariant_list;
    
    (*(*Pair up invariants with names to verify them *)                
    let inv' =
      
      List.map
        (fun t ->
          ("inv_"^(Numeral.string_of_numeral !count), t)
        )
        top_node_invariants_list
    in
    *)
    (*verify_invariants ts inv';*)
    
    (*Set number of invariants statistics*)
    Stat.set ((List.length top_node_invariants_list) + (Stat.get Stat.invgen_num_invs)) Stat.invgen_num_invs;
   
   (* (debug inv "The total number of invariant found =  %d" (List.length top_node_invariants_list) end);*)
    
    (*Send out top node invariants*)
    List.iter
      (fun inv ->
        (debug inv "%s" (Term.string_of_term (Term.eval_t (fun ft _ -> Term.construct ft) inv)) end);
        Event.invariant inv
                
      )
      top_node_invariants_list


(*Call BMC to refine implication graph*)
let rec refine_bmc_step lock_step_driver uf_defs invariants pre_model =
  
  (*Create candidate invariants for BASE to check and return to STEP *)
  let candidate_invariants 
    = mk_candidate_invariants invariants (LockStepDriver.get_k lock_step_driver) 
    
  in

  (* Call BMC until no properties disproved at current step*)
  match (LockStepDriver.query_base lock_step_driver candidate_invariants) with

  | None -> 
    
    candidate_invariants

  | Some model -> 
    
    (*Rebuild implicatioin graph with the model*)
    rebuild_graph uf_defs model (LockStepDriver.get_k lock_step_driver);
    
    (*Try to refine the implication graph further*)
    refine_bmc_step lock_step_driver uf_defs invariants model
       
  
(*Start invariants generation process*)
let rec start_inv_gen lock_step_driver all_candidate_terms ts invariants  =
      
  let uf_defs = TransSys.uf_defs ts in
  
  let candidate_invariants = 
    mk_candidate_invariants invariants (LockStepDriver.get_k lock_step_driver) in
  
  match candidate_invariants with
  
  | [] -> 
      
      (debug inv "No more candidate invariants!" end);
    
  | _ -> 
    
    Stat.set (Numeral.to_int (LockStepDriver.get_k lock_step_driver)) Stat.invgen_k;
    
    Stat.update_time Stat.invgen_total_time;        
    
    let candidate_invs = 
      refine_bmc_step lock_step_driver uf_defs invariants []
    
    in
    
    (*(debug inv "candidate_invs len  = %d" (List.length candidate_invs)  end);*)
    
    (* Call IND to prove invarance of candidates*)
    let props_not_kind, props_kind = 
      LockStepDriver.query_step lock_step_driver candidate_invs
      
    in 
    
    LockStepDriver.increment lock_step_driver;      
    
    (*Broadcast invariants*)
    send_out_invariants lock_step_driver ts all_candidate_terms (remove_trivial_invariants props_kind);
    
    (*Start inv_gen with remaining candidates*)
    start_inv_gen lock_step_driver all_candidate_terms ts (props_kind @ invariants)


(* Generate invariants from candidate terms*)
let inv_gen trans_sys = 
  
  (*Extract candidate terms from transition system*)
  (*candidate_terms is a list of pairs [(trans_symbol, [(type, {term_set of type})])]*)
  let candidate_terms = extract_candidate_terms trans_sys in
  
  (*bool_term is a list of pairs [(trans_symbol, {term_set})]*)
  let bool_terms =
    
    List.fold_left
    
      (fun accum (trans_symbol, term_set_list) ->
        
        let bool_term_set =
          
          try
              (List.assoc Type.t_bool term_set_list)
              
           with Not_found -> TTS.empty
          
         in
        
         if ((TTS.cardinal bool_term_set) < 3) || (TTS.is_empty bool_term_set) then 
         
           accum 
          
         else 
          (
            (trans_symbol, bool_term_set)::accum            
          )                  
      )
      [] 
      candidate_terms
    
  in    
  
 (* List.iter
    (fun (trans_s, t) ->
     
      (debug inv "Extract symbol trans = %s " (UfSymbol.string_of_uf_symbol trans_s) end);
      
      List.iter
        (fun (x, y) ->
          (debug inv "  Type = %s" (Type.string_of_type x) end); 
          TTS.iter
            (fun z ->
              (debug inv "Term = %s" (Term.string_of_term z) end);
            ) y
       ) t
  ) candidate_terms;*)
  
  
(*    List.iter
    (fun (trans_s, t) ->
     
      (debug inv "Extract symbol trans = %s   $$$$$$$$$$$$    " (UfSymbol.string_of_uf_symbol trans_s) end);
      
      TTS.iter
        (fun term ->
          (debug inv "  term = %s" (Term.string_of_term term) end); 

       ) t
  ) bool_terms;*)
  
  let lock_step_driver = LockStepDriver.create trans_sys in
  
  (*Start from k = 1 for checking two states invariants*)
  LockStepDriver.increment lock_step_driver;
  
  let uf_defs = TransSys.uf_defs trans_sys in
    
  if not (bool_terms = []) then
    
    (
      
      (*Add intial nodes to the implication graph *)
      List.iter
        (fun (_, terms_set) ->
            
          if not (TTS.is_empty terms_set) then
            (
                
              let terms_list = TTS.elements terms_set in
                
              (*Pick a term other than "true" or "false" as the representative for the equivalence class,*)
              let rep = pick_rep_term terms_list in                           
                
              (*Add an equivalence class to the implication graph along with "true" and "false" terms*)
              THT.add nodes_hashtl rep  (add_true_false_terms terms_list)
                
            );

        ) 
        bool_terms;
           
      start_inv_gen lock_step_driver candidate_terms trans_sys []
      
    )
    
  else
    
    (debug inv "No boolean candidate terms proposed!" end)

(* Entry point *)
let main trans_sys = 
  
  Stat.start_timer Stat.invgen_total_time;
  
  Event.set_module `INVGEN;
  
  inv_gen trans_sys


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
