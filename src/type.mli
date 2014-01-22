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

(** Types of terms

    A type has to be hash-consed to be used in hash-consed terms.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** Type of an expression *)
type kindtype = 
  | Bool
  | Int
  | IntRange of Numeral.t * Numeral.t
  | Real
  | BV of int
  | Array of t * t

(** Hashconsed type *)
and t

(** Return the value {!kindtype} in a hashconsed type *)
val node_of_type : t -> kindtype

(** {1 Hashtables, maps and sets} *)

(** Comparison function on types *)
val compare_types : t -> t -> int

(** Equality function on types *)
val equal_types : t -> t -> bool

(** Hashing function on types *)
val hash_type : t -> int

(** Hash table over variables *)
module TypeHashtbl : Hashtbl.S with type key = t

(** Set over variables *)
module TypeSet : Set.S with type elt = t

(** Map over variables *)
module TypeMap : Map.S with type key = t


(** {1 Constructor} *)

(** Hashcons a type *)
val mk_type : kindtype -> t

(** Return the boolean type *)
val mk_bool : unit -> t

(** Return the integer type *)
val mk_int : unit -> t 

(** Return the integer range type *)
val mk_int_range : Numeral.t -> Numeral.t -> t

(** Return the real decimal type *)
val mk_real : unit -> t

(** Return the bitvector type *)
val mk_bv : int -> t

(** Return the array type *)
val mk_array : t -> t -> t

(** Import a type from a different instance into this hashcons table *)
val import : t -> t 

(** The boolean type *)
val t_bool : t

(** The integer type *)
val t_int : t

(** The real decimal type *)
val t_real : t

(** {1 Predicates} *)

(** Return [true] if the type is the Boolean type *)
val is_bool : t -> bool

(** Return [true] if the type is an integer type *)
val is_int : t -> bool

(** Return [true] if the type is the real type *)
val is_real : t -> bool

(** Return [true] if the type is a bitvector type *)
val is_bv : t -> bool

(** Return [true] if the type is an array type *)
val is_array : t -> bool

(** {1 Pretty-printing} *)

(** Pretty-print a type *)
val pp_print_type_node : Format.formatter -> kindtype -> unit

(** Pretty-print a type *)
val pp_print_type : Format.formatter -> t -> unit

(** Return a string representation of a type *)
val string_of_type : t -> string


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
