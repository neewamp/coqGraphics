(* To DO: 1) Finish the draw line function 
          in the section for interp on line 89
          2) Think up different specifications that would be useful*)
(*           An example could be a specification that shows that draw
             rectangle actually draws a rectangle*)

(* Let me know if you have any questions *)

Require Import PArith String FMaps FMapAVL ExtrOcamlString.
Require Import Pnat QArith.


Require Export QArith.
(* We probably need a way to express background and forground idk maybe something in the pixel type?*)

(*Inductive color: Type :=
| Red : color
| Blue : color
| Green : color
| White : color. *)

Definition color := Z.
Definition Red := Zpos 1.
Definition Blue := Zpos 1.
Definition Green := Zpos 1.
Definition White := Zpos 1.


(* The type of a single pixel's location*)
Module pixel_l:=  PairOrderedType Z_as_OT Z_as_OT.
Definition point : Type := (Z * Z).

(* This is the map that we can use to define the state 
    hopefully i'm making it's type soundly*)
Module pix :=  FMapAVL.Make pixel_l.

Definition pixtype := pix.t.
Print pix.
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
| lineto : point -> point -> color -> g_com
(* | plots : list (Z * Z) -> unit -> g_com *)
(* | moveto : point -> unit -> g_com *)
(* | lineto : point -> g_com *)
(* Rec with the bottom left point followed by the top right.*)          
| draw_rect : point -> point -> color -> g_com
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
  }.

Definition distance (p1 p2 : point) : nat :=
  let dx := (fst p2) - (fst p1) in
  let dy := (snd p2) - (snd p1) in
  Z.to_nat (Z.sqrt ((Z.square dx) + (Z.square dy))).

Section interp.
  
  (* Notation "a # b" := (Qmake a b) (at level 55, no associativity) : Q_scope. *)
  Context {T : Type} `{graphics_prims T}.
  
  Fixpoint interpolate (t : T) (n : nat)
           (p1 p2 V: point) (D : nat) c : T :=
    match n with
    | O => draw_pixel t p1 c
    | 1%nat => draw_pixel t p1 c
    | S n' => let p1' := ( (fst p1) + (fst V) * (Z.of_nat (Nat.div n D )),                  (snd p1) + (snd V) * (Z.of_nat (Nat.div n D)))
    in
      draw_pixel (interpolate t n' p1' p2 V D c) p1 c 
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
  | S h',(x,y) => draw_hline (fill_rect_rc t p w h' c) (x,y+(Z.of_nat h')) c w
  end.  


(* this needs a couple things and then maybe it will work*)
  Definition interp_draw_line (t : T) (c : color)
             (p1 p2 : point) : T :=
    interpolate t ((distance p1 p2) - 1) p1 p2 ((fst p2) - (fst p1), (snd p2) - (snd p1) ) (distance p1 p2) c.
  

    (* draw_pixel t p1 c.  need to make this actually draw a line 
                          seems like a david thing*)
  Fixpoint interp (t : T) (e : g_com) : T :=
    match e with
    | open_graph s_size => update_state t s_size
    | resize_window s_size => update_state t s_size 
    | lineto p1 p2 c => interp_draw_line t c p1 p2
    | draw_rect (x,y) (w,h) c =>
        let w' := Z.to_nat w in
        let h' := Z.to_nat h in
        let t1 := draw_hline t (x,y) c w' in
        let t2 := draw_hline t1 (x,y+h) c w' in
        let t3 := draw_vline t2 (x,y) c h' in
                  draw_vline t3 (x+w,y) c h'
    | fill_rect p (w,h) c => fill_rect_rc t p (Z.to_nat w) (Z.to_nat h) c
    (*| draw_rect p1 p2 c =>
      match p1, p2 with
      | (x,y), (z,w) => (* lower-left and upper-right *)
        let t1 := interp_draw_line t c (x,y) (x,w) in
        let t2 := interp_draw_line t1 c (x,y) (z,y) in
        let t3 := interp_draw_line t2 c (x,w) (z,w) in
        let t4 := interp_draw_line t3 c (z,w) (z,y) in
        t4
      end
    *)
    | seq g1 g2 => let st := (interp t g1) in (interp st g1)
    end.

  Definition run (e : g_com) : T :=
    interp (init_state tt) e.
End interp.
