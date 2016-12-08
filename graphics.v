Require Import graphicsTypeClass ExtrOcamlString.
(*example Instances We would use the State that 
n         we defined above *)




(* Example very tentatively modelling extraction into ocaml*)

Definition OGState := unit. (* OCaml graphics state *)(* Maybe make this unit*)
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

Extract Inductive unit => "unit" [ "()" ].
Extract Constant initial_OGState => "()".
Extract Constant ocaml_graphics_init =>
  "(fun _ -> Graphics.open_graph "" 1920x1080"")".

Extract Constant ocaml_draw_pixel =>
"  (fun _ (p : point) c ->
    let rec int_of_z po =
  (match po with
   |Z0 -> 0
   |Zpos p'' ->
     (match p'' with
      | XH -> 1
      | XO p' -> 2 * int_of_z (Zpos p')
      | XI p' -> (2 * int_of_z (Zpos p')) + 1)
   |Zneg p'' ->
     (match p'' with
      | XH -> -1
      | XO p' -> 2 * int_of_z (Zneg p')
      | XI p' -> (2 * int_of_z (Zneg p')) + 1))
      in   Graphics.plot (int_of_z (fst p)) (int_of_z (snd p)); Graphics.set_color (int_of_z c));;
".

Open Scope Z_scope.

Definition prog := fill_rect (100,0) (300,400) Red;;
                             fill_rect (1000,1000) (1500,1500) Red.

Definition t : OGState := interp (init_state tt) prog.
Extract Inductive prod => "(*)"  [ "(,)" ].

Recursive Extraction t.
Extraction "test.ml" t.




  (* "(fun _ p c ->   *)
  (*    let rec int_of_pos p =  *)
  (*    (match p with *)
  (*    |Zpos p'' ->  *)
  (*      (match p'' with  *)
  (*        | XH -> 1 *)
  (*        | XO p' -> 2 * int_of_pos p' *)
  (*        | XI p' -> (2 * int_of_pos p') + 1) *)
  (*    |Zneg p'' ->  *)
  (*      (match p'' with  *)
  (*        | XH -> 1 *)
  (*        | XO p' -> 2 * int_of_pos p' *)
  (*        | XI p' -> (2 * int_of_pos p') + 1)) *)
  (*    in  *)
  (*    Graphics.set_color c; *)
  (*    Graphics.plot """" (int_of_pos p))". *)











(* Extract Constant camel_string "'x'"  => "let camel_string (s: char list) : string = *)
(* let r = String.create (List.length s) in *)
(* let rec fill pos = function *)
(* | [] -> r *)
(* | c :: s -> r.[pos] <- c; fill (pos + 1) s *)
(* in fill 0 s". *)


(* Extract Inductive g_com => g_com [ "open_graph" "resize_window" "close_graph" "plot" "plots" "moveto" "lineto" "draw_rect" " "]. *)



