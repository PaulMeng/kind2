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

(* We don't need to clean up anything *)
let on_exit () = ()

(* Hashtables for the implication graph*)

module THT = Term.TermHashtbl

(* Map of term representative to a term list it represents*)
let nodes_hashtl = Term.TermHashtbl.create 7

(* Map of term representative to a list of representatives (implication)*)
let outgoing_hashtl = Term.TermHashtbl.create 7

let incoming_hashtl = Term.TermHashtbl.create 7


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
let collect_subterms (fterm:Term.T.flat) (acc:((Type.t*Term.TermSet.t) list) list) : (Type.t*Term.TermSet.t) list=
  match fterm with
  | Term.T.App (s, l) as app ->
    
    let t = Term.construct app in
    
    let t_type = Term.type_of_term t in
    
    let f_list = 
      if Flags.invgen_bool_complement () then
        
        (t_type, Term.TermSet.singleton t)::(List.flatten acc)
        
      else 
        
        (t_type, Term.TermSet.union (Term.TermSet.singleton t) (Term.TermSet.singleton (Term.negate t)))::(List.flatten acc)
    in
    List.fold_left
      (fun accum' (t, s) ->
        merge_in [] (t, s) accum')
    []
    f_list
                  
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
    
(** Extract all subterms from a transition system *)  
let extract_terms ts =
  
  let uf_defs = ts.TransSys.uf_defs in
  
  let terms = List.map (fun (s, x) ->  (s, snd x)) uf_defs in
  
  let term_set = 
    List.map
    (fun (s, t) ->
      (s, (Term.eval_t collect_subterms t)))
    terms
  in
  
  List.map 
    (fun (s, t_list) -> 
      (s, 
      (List.map
         (fun (t, t_set)->
            (t, Term.TermSet.elements t_set)
          )
       t_list))) 
  term_set
  
(* Safely add an edge to the edge hashtables*)  
let edge_hashtbl_safe_add ht (n_1:Term.t) (n_2:Term.t):unit =  
  if THT.mem ht n_1 then
    THT.replace ht n_1 (n_2::(THT.find ht n_1))
  else
    THT.add ht n_1 [n_2]
    
(* Safely remove an edge from the edge hashtables*)
let edge_hashtbl_safe_remove ht n_1 n_2 =  
  if THT.mem ht n_1 then
    THT.replace ht n_1 (List.filter (fun t -> t <> n_2) (THT.find ht n_1))

(* Safely add a node to the node hashtable*)    
let node_hashtbl_safe_add ht n_1 n_2 =  
  if THT.mem ht n_1 then
    THT.replace ht n_1 n_2
  else
    THT.add ht n_1 n_2

(* Remove useless (isolated or empty) nodes*)
let clean_graph =
  (*Remove empty nodes and reroute edges around nodes*)
  THT.iter
    (fun k v ->
      if List.length v = 0 then
        THT.remove nodes_hashtl k;
        List.iter 
          (fun incoming_node ->
            List.iter
              (fun outgoing_node ->
                edge_hashtbl_safe_add outgoing_hashtl incoming_node outgoing_node;
                edge_hashtbl_safe_remove outgoing_hashtl incoming_node k; 
                edge_hashtbl_safe_remove incoming_hashtl outgoing_node k;
                edge_hashtbl_safe_add incoming_hashtl outgoing_node incoming_node
              )
            (THT.find outgoing_hashtl k) 
          )
        (THT.find incoming_hashtl k)
      )
   nodes_hashtl;
  
  (*Remove nodes of size less than 2 and does not have imcoming or outgoing edges*)
  THT.iter
    (fun r term_list ->
      if ((List.length term_list) < 2 
         &&
         List.length (THT.find outgoing_hashtl r) = 0
         &&
         List.length (THT.find incoming_hashtl r) = 0)
        then
          THT.remove nodes_hashtl r
        
    )
  nodes_hashtl

(* Update the graph based on the splits and old graph*)
let update_graph chains =
  let edges = 
    THT.fold
      (fun k v init ->
        List.fold_left
          (fun edges' t ->
            let source_chain = List.assoc k chains in
            let destination_chain = List.assoc t chains in
            if (((List.length (snd (fst source_chain))) = 0) && ((List.length (snd (snd destination_chain))) = 0)) then
              ((snd source_chain, fst destination_chain)::(fst source_chain, fst destination_chain)::(snd source_chain, snd destination_chain)::edges')
            else
              ((fst source_chain, fst destination_chain)::(snd source_chain, snd destination_chain)::edges')
          )
        init v    
      )
    outgoing_hashtl []
  in
  
  List.iter
    (fun (s, d) ->
      edge_hashtbl_safe_add outgoing_hashtl (fst s) (fst d);
      edge_hashtbl_safe_add incoming_hashtl (fst d) (fst s);
      node_hashtbl_safe_add nodes_hashtl (fst s) (snd s);
      node_hashtbl_safe_add nodes_hashtl (fst d) (snd d);     
    )
  (edges:((Term.t*(Term.t list))*(Term.t*(Term.t list))) list)

(** Split nodes based on the model*)
let rebuild_graph uf_defs model k =
  let chains = 
    THT.fold
      (fun rep term_list init ->
        let (t_list_1, t_list_0) =
          List.partition
            (fun t ->
              Eval.bool_of_value
                (Eval.eval_term uf_defs model (Term.bump_state k t))
            )
          term_list
        in
        if (List.length t_list_0) <> 0 && (List.length t_list_1) <> 0 then
          (
            edge_hashtbl_safe_add outgoing_hashtl (List.hd t_list_0) (List.hd t_list_1);
            edge_hashtbl_safe_add incoming_hashtl (List.hd t_list_1) (List.hd t_list_0);
            (rep, ((List.hd t_list_1, t_list_1), (List.hd t_list_0, t_list_0)))::init
          )
        else if (List.length t_list_0 <> 0) then
          (
            (* How to make a unique term for empty list ?*)
            let unique_term_rep = snd (Term.mk_named Term.t_true) in
            (rep, ((unique_term_rep, t_list_1), (List.hd t_list_0, t_list_0)))::init
          )
        else
          (
            let unique_term_rep = snd (Term.mk_named Term.t_false) in
            (rep, ((List.hd t_list_1, t_list_1), (unique_term_rep, t_list_0)))::init
          )
      )
    nodes_hashtl []
  in
  update_graph chains;
  clean_graph 

(* Make candidate invariants out of the graph*)
let mk_candidate_invariants () = 
  
  (*Make candidate invariants out of nodes*)
  let candidate_invariants =
    THT.fold
      (fun rep term_list accum ->
        (List.map
          (fun t ->
            Term.mk_eq [rep; t])
        (List.tl term_list))@accum)
    nodes_hashtl []
  in
  
  (*Make candidate invariants out of edges*)
  let candidate_invariants' =
    THT.fold
      (fun source destination_list accum ->
        (List.map
          (fun t ->
            Term.mk_implies [source; t])
        destination_list)@accum)
    outgoing_hashtl []
  in
  
  (candidate_invariants@candidate_invariants')

(*Call BMC to create stable implication graph*)
let rec create_stable_graph solver ts k candidate_invs =
  
  (* Call BMC until no properties disproved at current step*)
  let props_unknown, props_invalid = 
    
    Bmc.bmc_step true solver ts k candidate_invs
    
  in
  
  (*Record current bmc step*)
  bmcK := Numeral.succ k;
  
  (*rebuild the graph if some candidate invariants are disproved by BMC*)
  if List.length props_invalid <> 0 then
    
    let uf_defs = trans_sys.TransSys.uf_defs in
  
    (* Variables in property at step k *)
    let k_vars = Var.VarSet.elements (Term.vars_of_term p_k) in
  
    (* Model for variables of property at step k *)
    let k_model = S.get_model solver k_vars in
    
    rebuild_graph uf_defs k_model k;
        
    create_stable_graph solver ts (Numeral.succ k) (mk_candidate_invariants ())

let rec produce_invariants bmc_solver ind_solver ts ind_k invariants start = 
  
  if start then
    
    (*Create a stable implication graph by BMC*)
    create_stable_graph bmc_solver ts Numeral.zero (mk_candidate_invariants ());
  
  let props_k_ind, props_not_k_ind = 
    
    IndStep.ind_step 
      ind_solver 
      ts 
      [] 
      (list_subtract (mk_candidate_invariants ()) invariants)
      ind_k
    
  in
  
  (*Send out invariants props_k_ind*)
  List.iter
    (fun (name, term) -> Event.invariant `INVGEN term) 
  props_k_ind;
  
  if ((List.length props_not_k_ind) <> 0 && (Numeral.gt ind_k bmcK) ) then
    
    ( 
      create_stable_graph 
        bmc_solver 
        ts 
        (Numeral.succ bmcK) 
        (list_subtract (mk_candidate_invariants ()) invariants)
    );
    
  produce_invariants bmc_solver ind_solver ts  (Numeral.succ ind_k) (invariants@props_k_ind) false
  

(* Generate invariants from candidate terms*)
let inv_gen trans_sys = 
  
  (*Extract candidate terms from transition system*)
  let candidate_terms = extract_terms trans_sys in
  
  let bool_terms =
    List.fold_left
      (fun accum (symbol,l) ->
        (List.assoc Type.t_bool l)@accum
      )
    [] candidate_terms
  in
  
  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic trans_sys in
  
  (* Create BMC solver instance *)
  let bmc_solver = 
    Bmc.S.new_solver ~produce_assignments:true logic 
  in
  
  (* Create IND solver instance *)
  let ind_solver = 
    IndStep.S.new_solver ~produce_assignments:true logic 
  in
    
  if (List.length bool_terms) <> 0 then
    
    (
      
      THT.add nodes_hashtl Term.t_true (Term.t_true::Term.t_false::bool_terms);
      
      produce_invariants bmc_solver ind_solver trans_sys Numeral.zero [] true
      
    )
      
      
(*      let candidate_invariants = mk_candidate_invariants () in
      
      List.iter
      (fun t ->
        (debug inv "Candidate invariant:  %s" (Term.string_of_term t) end);
      ) 
      candidate_invariants
    )*)

(*    List.iter
    (fun (s, t) ->
      (debug inv "Extract symbol s = %s" (UfSymbol.string_of_uf_symbol s) end);
      List.iter
        (fun (x, y) ->
          (debug inv "  Type = %s" (Type.string_of_type x) end); 
          List.iter
            (fun z ->
              (debug inv "Term = %s" (Term.string_of_term z) end);) 
          y)
       t) 
  candidate_terms*)


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


(* Entry point *)
let main trans_sys = 
  inv_gen trans_sys;
  (* Run loop *)
  inv_gen_dummy 0


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
