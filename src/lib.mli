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

(** General-purpose library functions 

    @author Christoph Sticksel
*)

(** {1 Infinite-precision numbers and bit-vectors} *)

(** Constant bitvector *)
type bitvector

(** Return the length of a bitvector as a numeral *)
val length_of_bitvector : bitvector -> int

(** Convert a string to a bitvector

    Binary and hexadecimal notation is accepted as #b[01]+ and
    #x[0-9a-fA-F]+ as in the SMTLIB standard *)
val bitvector_of_string : string -> bitvector

(** Convert a hashconsed string to a bitvector, store all converted
    values in a cache *)
val bitvector_of_hstring : HString.t -> bitvector

(** Convert a hashconsed string to a Boolean value *)
val bool_of_hstring : HString.t -> bool

(** Pretty-print a constant bitvector in binary format *)
val pp_print_bitvector_b : Format.formatter -> bitvector -> unit

(** Pretty-print a constant bitvector in hexadeciaml format *)
val pp_print_bitvector_x : Format.formatter -> bitvector -> unit

(** {1 Integer functions} *)

(** [safe_hash_interleave h m i] compute [m * h + i] and makes sure
    that the result does not overflow to a negtive number *)
val safe_hash_interleave : int -> int -> int -> int

(** {1 List functions} *)

(** [chain_list \[e1; e2; ...\]] is [\[\[e1; e2\]; \[e2; e3\]; ... \]] *)
val chain_list : 'a list -> 'a list list 

(** Return a list containing all values in the first list that are not
    in the second list *)
val list_subtract : 'a list -> 'a list -> 'a list 

(** From a sorted list return a list with physical duplicates removed *)
val list_uniq : 'a list -> 'a list

(** Merge two sorted lists without physical duplicates to a sorted list without
   physical duplicates *)
val list_merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

(** From two sorted lists without physical duplicates return a sorted
    list without physical duplicates containing elements in both
    lists *)
val list_inter_uniq :  ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

(** From two sorted lists without physical duplicates return a sorted
    list without physical duplicates containing elements in the first
    but not in the second list *)
val list_diff_uniq :  ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

(** For two sorted lists without physical duplicates return true if
    the first list contains a physically equal element for each element
    in the second list *)
val list_subset_uniq :  ('a -> 'a -> int) -> 'a list -> 'a list -> bool

(** Lexicographic comparison of lists *)
val compare_lists : ('a -> 'a -> int) -> 'a list -> 'a list -> int 

(** {1 Pretty-printing helpers} *)

(** Pretty-print a list with given separator 

    [pp_print_list p s f l] pretty-prints the elements in the list [l]
    by calling the pretty-printer [p] on each, separating the elements
    by printing the string [s] and marking the position after each [s]
    as a good break. Use this after opening a pretty-printing box to
    make use of the break hints.

    In order to get line breaks between the elements, do not use a
    line feed character [\n] as separator, this might mess up
    indentation. Instead wrap the list into a vertical box with the
    format string [@\[<v>%a@\]] and the empty string as separator.
*)
val pp_print_list : (Format.formatter -> 'a -> unit) -> ('b, Format.formatter, unit) format -> Format.formatter -> 'a list -> unit

(** Pretty-print an option type *)
val pp_print_option : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit

(** Pretty-print into a string *)
val string_of_t : (Format.formatter -> 'a -> unit) -> 'a -> string 


(** Return the strings as a parenthesized and space separated list *)
val paren_string_of_string_list : string list -> string


(** {1 System functions} *)

(** Kind modules *)
type kind_module = [ `PDR | `BMC | `IND | `INVGEN | `INVMAN | `Interpreter ]

(** Wallclock timeout *)
exception TimeoutWall

(** CPU timeout *)
exception TimeoutVirtual

(** System signal caught *)
exception Signal of int

(** String representation of signal *)
val string_of_signal : int -> string 

(** Pretty-print the termination status of a process *)
val pp_print_process_status : Format.formatter -> Unix.process_status -> unit

(** Raise exception on signal *)
val exception_on_signal : int -> 'a

(** Pretty-print the name of a kind module *)
val pp_print_kind_module : Format.formatter -> kind_module -> unit

(** String representation of a process type *)
val string_of_kind_module : kind_module -> string 

(** Kind module of a string *)
val kind_module_of_string : string -> kind_module

(** Sleep for seconds, resolution is in ms *)
val minisleep : float -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
