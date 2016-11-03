Require Import ZArith String FMaps FMapAVL.
(* Todo implement key functions from the graphics library of ocaml.  Possibly as an abstract syntax tree.*)


(* We probably need a way to express background and forground idk maybe something in the pixel type?*)

(*Module color : *)
(* Inductive color: Type := *)
(* | Red : color *)
(* | Blue : color *)
(* | Green : color. *)

(*Ok so we should probably implement colors as RBG values eventually but the inductive type might be easier but I don't want to order it now.*)


(* This is ugly and prolly needs to be changed I just don't want to deal with making a better structure that is also an ordered type.  Maybe it's not needed for the map though idk*)
Module color1 := PairOrderedType Z_as_OT Z_as_OT.
Module color := PairOrderedType color1 Z_as_OT.

(* The type of a single pixel*)
Module pixel_l := PairOrderedType Z_as_OT Z_as_OT.
(* A pixel is a tuple (location, color)*)
Module pixel := PairOrderedType pixel_l color.

Print pixel.


(* Here is a map that we can use for state.*)
Open Scope Z_scope.
Module pix := FMapAVL.Make pixel_l.
Print pix.

(* We should put in some notation to make the map easier 
   to use but I think this is enough to get the general idea.*)
Definition update (p : pixel_l.t) (pelet : pixel.t) (orig : pix.t pixel.t) : pix.t pixel.t  := pix.add p pelet orig.

Definition st := pix.t pixel.t.


(*The syntax of commands in the ocaml graphics library*)
(*I might be fucking up the types of this thing but whatever*)
Inductive g_com : Type :=
| open_graph : string -> unit -> g_com
| close_graph : unit -> unit -> g_com
| plot : Z -> Z -> unit -> g_com
| plots : list (Z * Z) -> unit -> g_com
| moveto : Z -> Z -> unit -> g_com
| lineto : st -> Z -> Z -> st -> g_com (* so i added st instead of unit idk  if that makes sense*)
| draw_rect : Z -> Z -> Z -> Z -> unit -> g_com.





