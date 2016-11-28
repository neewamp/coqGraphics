Require Import graphicsTypeClass ExtrOcamlString.
(*example Instances We would use the State that 
n         we defined above *)




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
     Graphics.plot """" (int_of_pos p))".


Definition t : OGState := interp (init_state tt) prog1.

(* Recursive Extraction t prog1. *)
(* Extraction "test.ml" t. *)










(* Extract Constant camel_string "'x'"  => "let camel_string (s: char list) : string = *)
(* let r = String.create (List.length s) in *)
(* let rec fill pos = function *)
(* | [] -> r *)
(* | c :: s -> r.[pos] <- c; fill (pos + 1) s *)
(* in fill 0 s". *)


(* Extract Inductive g_com => g_com [ "open_graph" "resize_window" "close_graph" "plot" "plots" "moveto" "lineto" "draw_rect" " "]. *)



