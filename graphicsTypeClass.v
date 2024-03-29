Require Import ZArith String FMaps FMapAVL.

Definition rgb : Type := (Z * Z * Z).

Definition toRGB (c : Z) : rgb :=
((Zmod c 256),(Zmod (Zdiv c 256) 256),(Zmod (Zdiv c 65536) 256)).

Definition fromRGB(c : rgb) : Z :=
match c with
| (r,g,b) => r + (g * 256) + (b * 65536)
end.


Open Scope Z_scope.

Definition color := Z.
Definition Black := fromRGB(0,0,0).
Definition Red := fromRGB (0,0,255).
Definition Blue := fromRGB (255,0,0).
Definition Green := fromRGB (0,255,0).
Definition White := fromRGB(255,255,255).




(* The type of a single pixel's location*)
Module pixel_l:=  PairOrderedType Z_as_OT Z_as_OT.
Definition point : Type := (Z * Z).

(* This is the map that we can use to define the state 
    hopefully i'm making it's type soundly*)
Module pix :=  FMapAVL.Make pixel_l.

Definition pixtype := pix.t.
(*The state is a map and a screen size*)

Open Scope Z_scope.
(* We should put in some notation to make the map easier  *)
(*    to use but I think this is enough to get the general idea.*)
Definition update (p : pixel_l.t) (pelet : color)
  (orig : pix.t color) : pix.t color := (pix.add p pelet) orig.

Program Definition emptyST  := pix.add (1,1) White _.
Next Obligation.
  apply pix.empty.
  Defined.


Program Definition p := update (1,2) Red emptyST.

Definition p1 := pix.add (2,2) Blue p.


(* We need two different functions like ocaml stuff and stuff that is in coq and a type class that could take and differentiate the two.*)
Inductive g_com : Type :=
| draw_pix : point -> color -> g_com
| open_graph : point -> g_com
| resize_window : point  -> g_com
(* | close_graph : unit -> unit -> g_com *)
| lineto : point -> point -> color -> g_com
(* | draw_circle : point -> Z -> g_com *)
(* | plots : list (Z * Z) -> unit -> g_com *)
(* | moveto : point -> unit -> g_com *)
| draw_rect : point -> point -> color -> g_com
(* Rec with the bottom left point followed by the top right.*)          
| fill_rect : point -> point -> color -> g_com
| seq : g_com -> g_com -> g_com.

Notation "a ;; b" := (seq a b) (at level 50, left associativity).

(*These are the basic 
  primitives that we build everything from*)

Class graphics_prims (T :Type) :=
  mkGraphicsPrims
    {
      init_state : unit -> T;
      update_state : T -> point -> T;
      (*Add an update color*)
      draw_pixel : T -> point -> color -> T;
      eq : T -> T -> Prop;
      eq_refl : forall x : T, eq x x;
      eq_sym : forall x y : T, eq x  y -> eq y x;
      eq_trans : forall x y z : T, eq x  y -> eq y z -> eq x z;
      pix_ok : forall p1 p2 c1 c2 (t : T),
          p1 <> p2 ->
          eq (draw_pixel (draw_pixel t p2 c1) p1 c2)
             (draw_pixel (draw_pixel t p1 c2) p2 c1)
  }.


Definition distance (p1 p2 : point) : Z :=
  let dx := (fst p2) - (fst p1) in
  let dy := (snd p2) - (snd p1) in
   (Z.sqrt ((Z.square dx) + (Z.square dy))).

Definition disVec (p1 p2 : point) := 
  ((fst p2) - (fst p1), (snd p2) - (snd p1)).

Section interp.

  Context {T : Type} `{graphics_prims T}.

  (* Fixpoint draw_circle_aux (t : T) (p1 : point) *)
  (*          (x : Z) (y : Z) (err : Z) :=  *)
  (*   match  *)
(* This is a integer function to draw circles.  It just needs to be 
   recursive. *)
(* void drawcircle(int x0, int y0, int radius) *)
(* {    int x = radius; *)
(*     int y = 0; *)
(*     int err = 0; *)
(*     while (x >= y) *)
(*     { *)
(*         putpixel(x0 + x, y0 + y); *)
(*         putpixel(x0 + y, y0 + x); *)
(*         putpixel(x0 - y, y0 + x); *)
(*         putpixel(x0 - x, y0 + y); *)
(*         putpixel(x0 - x, y0 - y); *)
(*         putpixel(x0 - y, y0 - x); *)
(*         putpixel(x0 + y, y0 - x); *)
(*         putpixel(x0 + x, y0 - y); *)

(*         y += 1; *)
(*         err += 1 + 2*y; *)
(*         if (2*(err-x) + 1 > 0) *)
(*         { *)
(*             x -= 1; *)
(*             err += 1 - 2*x; *)

(*         } *)
(*     } *)
(* } *)
  
  Fixpoint interpolate (t : T) (i : nat)
           (p1 p2 V: point) (num_points : Z) c : T :=
    match i with
    | O => draw_pixel t p1 c
    | 1%nat => draw_pixel t p1 c
    | S i' => let p1' :=
                  (((fst p1) + (fst V) * (Z.of_nat i) / num_points),
                  ((snd p1) + (snd V) * (Z.of_nat i) / num_points))
    in
      draw_pixel (interpolate t i' p1 p2 V num_points c) p1' c 
    end.

  Fixpoint draw_vline (t : T) (p : point) (c : color) (h : nat) : T :=
    match h,p with
    | O, _ => t
    | S h', (x,y) => draw_pixel (draw_vline t p c h') (x,y+(Z.of_nat h')) c
    end.

  Fixpoint draw_hline (t : T) (p : point) (c : color) (w : nat) : T :=
  match w,p with
  | O, _ => t
  | S w', (x,y) => draw_pixel (draw_hline t p c w') (x+(Z.of_nat w'),y) c
  end.

  Fixpoint fill_rect_rc (t : T) (p : point) (w h : nat) (c : color) : T :=
  match h,p with
  | O,_ => t
(*| S h',(x,y) => draw_hline (fill_rect_rc t p w h' c) (x,y+(Z.of_nat h')) c w*)
  | S h',(x,y) => draw_hline (fill_rect_rc t p w h' c) (x,y+Z.of_nat h') c w
  end.  


  Definition interp_draw_line (t : T) (c : color)
             (p1 p2 : point) : T :=
    interpolate t (Z.to_nat (distance p1 p2) - 1) p1 p2 ((fst p2) - (fst p1), (snd p2) - (snd p1) ) (distance p1 p2) c.
  

  Fixpoint interp (t : T) (e : g_com) : T :=
    match e with
    | draw_pix p c => draw_pixel t p c
    | open_graph s_size => update_state t s_size
    | resize_window s_size => update_state t s_size 
    | lineto p1 p2 c => let st := interp_draw_line t c p1 p2 in 
      let st' := draw_pixel st p1 c in  draw_pixel st' p2 c
    | draw_rect (x,y) (w,h) c =>
        let w' := Z.to_nat w in
        let h' := Z.to_nat h in
        let t1 := draw_hline t (x,y) c w' in
        let t2 := draw_hline t1 (x,y+h) c w' in
        let t3 := draw_vline t2 (x,y) c h' in
                  draw_vline t3 (x+w,y) c h'
    | fill_rect p (w,h) c => fill_rect_rc t p (Z.to_nat w) (Z.to_nat h) c
    | seq g1 g2 => let st := (interp t g1) in (interp st g2)
    end.

  Definition run (e : g_com) : T :=
    interp (init_state tt) e.

  Inductive DrawPixConst : T -> Type :=
  | initSt :  DrawPixConst (init_state tt)
  | updateSt : forall (t : T) s_size, DrawPixConst t -> 
      DrawPixConst (update_state t s_size)
  | drawPix : forall (t : T) p c, DrawPixConst t ->
      DrawPixConst (draw_pixel t p c).                                  

  (* Definition rebuild_g_com (g : g_com) : list  *)
  Theorem EqualStates : forall (t : T) p1 p2 c1 c2,
      p1 <> p2 -> 
      eq (interp t (draw_pix p1 c1 ;; draw_pix p2 c2))
      (interp t (draw_pix p2 c2 ;; draw_pix p1 c1)).
    Proof.
      intros.
      destruct p0,p2.
      simpl.
      destruct H.
      simpl in *.
      auto.
    Qed.
    



  
End interp.
