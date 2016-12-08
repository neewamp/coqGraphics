Require Import graphicsTypeClass.

Record pixelState :=
  mkPState
  {
    screen_state : pix.t color;
    screen_size : point; 
  }.
Program Definition init ( s_ : unit) := mkPState _ (1020, 780).
Next Obligation.
  apply pix.empty.
  Defined.

(*Our usefule instance that still needs some additions but includes a 
  way to make an initial state update the screen size and draw a pixel*)
Instance pixelMap_graphics_prims : graphics_prims pixelState :=
  mkGraphicsPrims
    pixelState
    (init)
    (fun s p => mkPState (screen_state s) p)
    (fun s p c => mkPState (update p c (screen_state s)) (screen_size s)).

Definition prog1 : g_com :=
   lineto (1,2) (1,4) Red.
  (* draw_rect (1,2) (3,4) Red. *)


Fixpoint toListPair (l : list (pix.key * color)) : list (pix.key):=
  match l with
  | nil => nil
  | cons (h, c) t => cons h (toListPair t)
  end.

Definition hi := (pix.elements (screen_state (interp (init_state tt) prog1))).

