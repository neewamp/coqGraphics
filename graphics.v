Require Import graphicsTypeClass ExtrOcamlString.

Definition OGState := unit.

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
Definition prog := lineto (100,200) (1700,900) Red.



Definition prog1 := draw_rect (100,0) (300,1000) Black;;
                             draw_rect (400,350) (300,200) Red;;
                             draw_rect  (700,0) (300, 1000) Black;;
                             draw_rect (1200,0) (200,500) Blue;;
                             draw_rect (1250,700) (100,100) Green.

Definition t : OGState := interp (init_state tt) prog.
Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "test.ml" t.



