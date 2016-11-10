(* To DO: 1) Finish the draw line function 
          in the section for interp on line 89
          2) Think up different specifications that would be useful*)

(* Let me know if you have any questions *)

Require Import PArith String FMaps FMapAVL ExtrOcamlString.
(*So sams idea is to idendify primatives that are live within the graphics functions and to verify everything with respect to those primatives*)



(* We probably need a way to express background and forground idk maybe something in the pixel type?*)

Inductive color: Type :=
| Red : color
| Blue : color
| Green : color
| White : color.


(* The type of a single pixel's location*)
Module pixel_l:=  PairOrderedType Positive_as_OT Positive_as_OT.
Definition point : Type := (positive * positive).

(* This is the map that we can use to define the state 
    hopefully i'm making it's type soundly*)
Module pix :=  FMapAVL.Make pixel_l.

Definition pixtype := pix.t.
Print pix.
(*The state is a map and a screen size*)
Record State :=
  mkState
  {
    screen_state : pix.t color;
    screen_size : point;
  }.

Open Scope positive_scope.
(* We should put in some notation to make the map easier  *)
(*    to use but I think this is enough to get the general idea.*)
Definition update (p : pixel_l.t) (pelet : color)
  (orig : pix.t color) : pix.t color := (pix.add p pelet) orig.

Program Definition emptyST  := pix.add (1,1) White _.
Next Obligation.
  apply pix.empty.
  Defined.


Program Definition p := update (1,2) Red emptyST.
Print p.

Definition p1 := pix.add (2,2) Blue p.
Compute pix.find (1,1) p1.

(* Maybe we need a state monad I don't 
   know where it would help currently
   Maybe when we define the semantics we just make it a function/
   relation that changes the state*)
(*Function interp (s : state) (exp : g_com) : state*)

(* We need two different functions like ocaml stuff and stuff that is in coq and a type class that could take and differentiate the two.*)


Inductive g_com : Type :=
| open_graph : point -> g_com
| resize_window : point  -> g_com
(* | close_graph : unit -> unit -> g_com *)
| plot : point -> point -> color -> g_com
(* | plots : list (Z * Z) -> unit -> g_com *)
(* | moveto : point -> unit -> g_com *)
(* | lineto : point -> g_com *)
(* Rec with the bottom left point followed by the top right.*)          
| draw_rect : point -> point -> color -> g_com
| seq : g_com -> g_com -> g_com.

Notation "a ;; b" := (seq a b) (at level 50, left associativity).

(*These are going to be the basic 
  functions that we build everything from*)
Class graphics_prims (T :Type) :=
  mkGraphicsPrims
    {
      init_state : unit -> T;
      update_state : T -> point -> T;
    (*This might have to take a color 
      or maybe we need to have a current 
      color in the state, feels more like the ocaml library*)
      draw_pixel : T -> point -> color -> T;
  }.

Section interp.
  Context {T : Type} `{graphics_prims T}.

  Definition interp_draw_line (t : T) (c : color)
                                (p1 p2 : point) : T :=
    draw_pixel t p1 c. (* need to make this actually draw a line 
                          seems like a david thing*)
  Fixpoint interp (t : T) (e : g_com) : T :=
    match e with
    | open_graph s_size => update_state t s_size
    | resize_window s_size => update_state t s_size 
    | plot p1 p2 c => interp_draw_line t c p1 p2
    | draw_rect p1 p2 c =>
      match p1, p2 with
      | (x,y), (z,w) => (* lower-left and upper-right *)
        let t1 := interp_draw_line t c (x,y) (x,w) in
        let t2 := interp_draw_line t1 c (x,y) (z,y) in
        let t3 := interp_draw_line t2 c (x,w) (z,w) in
        let t4 := interp_draw_line t3 c (z,w) (z,y) in
        t4
      end
    | seq g1 g2 => let st  := (interp t g1) in (interp st g1)
    end.

  Definition run (e : g_com) : T :=
    interp (init_state tt) e.
End interp.

(*example Instances We would use the State that 
         we defined above *)


Record boolState : Type :=
  mkStateB {
      b : bool
    }.

Instance boolState_graphics_prims : graphics_prims boolState :=
  mkGraphicsPrims
    boolState
    (fun (_:unit) => mkStateB false)
    (fun s p => mkStateB (negb (b s)))
    (fun s p c => mkStateB (negb (b s))).

Open Scope positive_scope.

Definition prog1 : g_com :=
  draw_rect (1,2) (3,4) Red.

Compute interp (init_state tt) prog1. 





(* Example very tentatively modelling extraction into ocaml*)

Axiom OGState : Type. (* OCaml graphics state *)(* Maybe makes this unit*)
Axiom initial_OGState : OGState.

(* OCaml graphics operations *)
Definition ocaml_graphics_init : unit -> OGState :=
  fun _ => initial_OGState.
Definition ocaml_update_state : OGState -> point -> OGState :=
  fun (s : OGState) p => s.
Definition ocaml_draw_pixel : OGState -> point -> color -> OGState :=
  fun (s:OGState) _ _ => s.

Instance OGState_graphics_prims : graphics_prims OGState :=
  mkGraphicsPrims
    OGState
    ocaml_graphics_init
    ocaml_update_state
    ocaml_draw_pixel.

Require Import Ascii String.
Definition s : string := "abc".
Print s.

Definition newline : ascii := ascii_of_pos 10.

Require Import List. Import ListNotations.
(* Maybe we can make a print function
   that makes a string of the buffer*)
Definition buf : string :=
  String newline EmptyString ++ 
  "                   .              " ++ String newline EmptyString ++
  "                  ...             " ++ String newline EmptyString ++
  "                 .....            " ++ String newline EmptyString ++
  "                  ...             " ++ String newline EmptyString ++
  "                   .              ".
Compute buf.

Extract Constant OGState => "unit".
Extract Constant initial_OGState => "()".

Extract Constant ocaml_graphics_init =>
  "(fun _ -> Graphics.open_graph ())".
Extract Constant ocaml_draw_pixel =>
  "(fun _ p c -> 
     let rec int_of_pos p = 
       (match p with 
         | XH -> 1
         | XO p' -> 2 * int_of_pos p'
         | XI p' -> (2 * int_of_pos p') + 1)
     in 
     Graphics.set_color c;
     Graphics.draw_pixel """" (int_of_pos p))".

Definition t : OGState := interp (init_state tt) prog1.

Recursive Extraction t.
Extraction "test.ml" t.










(* Extract Constant camel_string "'x'"  => "let camel_string (s: char list) : string = *)
(* let r = String.create (List.length s) in *)
(* let rec fill pos = function *)
(* | [] -> r *)
(* | c :: s -> r.[pos] <- c; fill (pos + 1) s *)
(* in fill 0 s". *)


(* Extract Inductive g_com => g_com [ "open_graph" "resize_window" "close_graph" "plot" "plots" "moveto" "lineto" "draw_rect" " "]. *)



Require Import ExtrOcamlPosInt.
Extraction Language Ocaml.

Extraction "export.ml"  g_com program1.