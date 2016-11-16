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
| lineto : point -> point -> color -> g_com
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

Notation "a # b" := (Qmake a b) (at level 55, no associativity) : Q_scope.


Definition Qabs (q : Q) : Q := 
match q with
| Z0 # d => q
| (Zpos n) # d => q
| (Zneg n) # d => (Zpos n) # d
end.

Require Import Coq.PArith.BinPos.



Fixpoint pos_to_nat (p : positive) : nat :=
match p with
| xH => S O
| xO p' => plus (pos_to_nat p') (pos_to_nat p')
| xI p' => plus (plus (pos_to_nat p') (pos_to_nat p')) (S O)
end.


Fixpoint nat_to_pos (n : nat) : positive :=
match n with
| O => xH
| S n' => Pos.succ (nat_to_pos n')
end.



Section interp.
  
  Notation "a # b" := (Qmake a b) (at level 55, no associativity) : Q_scope.
  Context {T : Type} `{graphics_prims T}.
  
  Fixpoint draw_line_rc (t : T) (p : point)
           (c : color)  (i : nat) (er der: Q) : T :=
    match i with
    | O => draw_pixel t p c
    | S i' => 
      match p with
      | (x,y) => draw_pixel 
       (if Qle_bool (Qmake 1 1) (Qplus er der)
        then draw_line_rc t (x,y+1) c i'
                          (Qplus der (Qminus er (Qmake 1 1))) der
          else if Qle_bool  (Qplus er der) (Qmake (Zneg 1) 1)
               then draw_line_rc t (x,y-1) c i'
                                 (Qplus der (Qplus er (Qmake 1 1))) der
               else draw_line_rc t p c i' (Qplus der er) der)
                   ((x + (nat_to_pos i)),y) c
      end  
    end.
  
  Fixpoint draw_vline (t : T) (p : point) (c : color) (h : nat) : T :=
    match h,p with
    | O, _ => draw_pixel t p c
    | S h', (x,y) => draw_pixel (draw_vline t p c h') (x,y+(nat_to_pos h)) c
    end.
  
  Definition interp_draw_line (t : T) (c : color)
             (p1 p2 : point) : T :=
  match p1,p2 with
  | (x1,y1),(x2,y2) => draw_line_rc t p1 c (pos_to_nat (x2 - x1)) (-1 # 1) ((Zpos (y2 - y1)) # (x2 - x1)) 
  end.
    (* draw_pixel t p1 c.  need to make this actually draw a line 
                          seems like a david thing*)
  Fixpoint interp (t : T) (e : g_com) : T :=
    match e with
    | open_graph s_size => update_state t s_size
    | resize_window s_size => update_state t s_size 
    | lineto p1 p2 c => interp_draw_line t c p1 p2
    | draw_rect p1 p2 c =>
      match p1, p2 with
      | (x,y), (z,w) => (* lower-left and upper-right *)
        let t1 := interp_draw_line t c (x,y) (x,w) in
        let t2 := interp_draw_line t1 c (x,y) (z,y) in
        let t3 := interp_draw_line t2 c (x,w) (z,w) in
        let t4 := interp_draw_line t3 c (z,w) (z,y) in
        t4
      end
    | seq g1 g2 => let st := (interp t g1) in (interp st g1)
    end.

  Definition run (e : g_com) : T :=
    interp (init_state tt) e.
End interp.