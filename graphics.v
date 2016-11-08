Require Import ZArith String FMaps FMapAVL ExtrOcamlString.


(* Todo implement key functions from the graphics library of ocaml.  Possibly as an abstract syntax tree.*)


(* We probably need a way to express background and forground idk maybe something in the pixel type?*)

Inductive color: Type :=
| Red : color
| Blue : color
| Green : color.


(* The type of a single pixel's location*)
Module pixel_l:=  PairOrderedType Z_as_OT Z_as_OT.

(* Here is a map that we can use for state.*)

Module pix :=  FMapAVL.Make pixel_l.

Definition pixtype := pix.t pixel_l.t.

Print pix.


Open Scope Z_scope.
(* We should put in some notation to make the map easier  *)
(*    to use but I think this is enough to get the general idea.*)
Definition update (p : pixel_l.t) (pelet : color)
  (orig : pix.t color) : pix.t color := (pix.add p pelet) orig.

Program Definition p := update (1,2) Red _.
Next Obligation.
apply pix.empty.
Defined.
Print p.

Definition p1 := pix.add (2,2) Blue p.
Compute pix.find (1,0) p1.


Definition st := pix.t. (*t pixel_l.t.*)


(*The syntax of commands in the ocaml graphics library*)
(* Maybe we need a state monad I don't 
   know where it would help currently
   Maybe when we define the semantics we just make it a function/
   relation that changes the state*)


Inductive g_com : Type :=
| open_graph : string -> unit -> g_com.
(* | resize_window : Z -> Z -> unit -> g_com *)
(* | close_graph : unit -> unit -> g_com *)
(* | plot : Z -> Z -> unit -> g_com *)
(* | plots : list (Z * Z) -> unit -> g_com *)
(* | moveto : Z -> Z -> unit -> g_com *)
(* | lineto : Z -> Z -> g_com *)
(* | draw_rect : Z -> Z -> Z -> Z -> unit -> g_com *)
(* | seq : g_com -> g_com -> g_com. *)

Extract Inductive nat => int [ "0" "succ" ]
       "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Axiom fill : Type -> Type -> Type.
Axiom char : Type.
Axiom create : Type -> Type.
Axiom s : char.
Axiom rpos : Type.



(* Definition camel_string (s : char) : string :=  *)
(*   let r := create (length s) in *)
(*   Fixpoint fill pos : string := "". *)

Axiom name :Type.

Axiom camel_string : Type -> Type.
Axiom Y : Set -> Set -> Set.
Extract Constant Y "'a" "'b" => " 'a*'b ".


Extract Constant camel_string "'x'"  => "let camel_string (s: char list) : string =
let r = String.create (List.length s) in
let rec fill pos = function
| [] -> r
| c :: s -> r.[pos] <- c; fill (pos + 1) s
in fill 0 s".

Extract Inductive g_com => g_com [ "open_graph (camel_string x)"].

Definition program1 := open_graph "200,300".


Definition hi : string := "hi".



Require Import Coq.extraction.ExtrOcamlZInt.
Extraction Language Ocaml.

Extraction "export.ml" camel_string pix g_com program1.