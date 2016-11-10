Require Import ZArith String FMaps FMapAVL ExtrOcamlString.
(*So sams idea is to idendify primatives that are live within the graphics functions and to verify everything with respect to those primatives*)



(* We probably need a way to express background and forground idk maybe something in the pixel type?*)

Inductive color: Type :=
| Red : color
| Blue : color
| Green : color
| White : color.


(* The type of a single pixel's location*)
Module pixel_l:=  PairOrderedType Z_as_OT Z_as_OT.


(* This is the map that we can use to define the state 
    hopefully i'm making it's type is sound*)
Module pix :=  FMapAVL.Make pixel_l.


Definition pixtype := pix.t.



Print pix.
Record State :=
  {
    screen_state : pix.t pixel_l.t;
    screen_size : pixel_l.t;
  }.







Open Scope Z_scope.
(* We should put in some notation to make the map easier  *)
(*    to use but I think this is enough to get the general idea.*)
Definition update (p : pixel_l.t) (pelet : color)
  (orig : pix.t color) : pix.t color := (pix.add p pelet) orig.

Program Definition emptyST  := pix.add (0,0) White _.
Next Obligation.
  apply pix.empty.
  Defined.


Program Definition p := update (1,2) Red _.
Next Obligation.
apply pix.empty.
Defined.
Print p.

Definition p1 := pix.add (2,2) Blue p.
Compute pix.find (1,0) p1.





(*The syntax of commands in the ocaml graphics library*)
(* Maybe we need a state monad I don't 
   know where it would help currently
   Maybe when we define the semantics we just make it a function/
   relation that changes the state*)


(* Definition open_graph : string -> unit. *)

(*Function interp (s : state) (exp : g_com) : state*)

(* We need two different functions like ocaml stuff and stuff that is in coq and a type class that could take and differentiate the two.*)

Class graph_primitive (T :Type) (I : Type) :=
  {
    open_graph : T -> (*Or make this a string*) I -> T;
    resize_window : T -> Z -> Z -> T;
    plot : T -> Z -> Z -> T
  }.

Fixpoint 


(* Axioms for essential functions*)

Inductive g_com : Type :=
| open_graph : string -> g_com
| resize_window : Z -> Z  -> g_com
| close_graph : unit -> unit -> g_com
| plot : Z -> Z -> unit -> g_com
| plots : list (Z * Z) -> unit -> g_com
| moveto : Z -> Z -> unit -> g_com
| lineto : Z -> Z -> g_com
| draw_rect : Z -> Z -> Z -> Z -> unit -> g_com
| seq : g_com -> g_com -> g_com.

Notation "a ;; b" := (seq a b) (at level 50, left associativity).


(* Definition camel_string (s : char) : string :=  *)
(*   let r := create (length s) in *)
(*   Fixpoint fill pos : string := "". *)


(* Axiom camel_string : Type -> Type. *)
(* Axiom Y : Set -> Set -> Set. *)
(* Extract Constant Y "'a" "'b" => " 'a*'b ". *)


(* Extract Constant camel_string "'x'"  => "let camel_string (s: char list) : string = *)
(* let r = String.create (List.length s) in *)
(* let rec fill pos = function *)
(* | [] -> r *)
(* | c :: s -> r.[pos] <- c; fill (pos + 1) s *)
(* in fill 0 s". *)
Open Scope Z_scope.
(*There are still commas between this stuff in program 1 but I guess we have the idea, and can hope gordan can fix this.*)

(*So We should move on to actually modelling what these commands do in coq.*)

Extract Inductive g_com => g_com [ "open_graph" "resize_window" "close_graph" "plot" "plots" "moveto" "lineto" "draw_rect" " "].

Definition program1 : g_com := open_graph "200,300";;resize_window 200 300.


Require Import ExtrOcamlZInt.
Extraction Language Ocaml.

Extraction "export.ml"  g_com program1.