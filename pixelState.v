Require Export  graphicsTypeClass.
Module pix_prop := FMapFacts.Properties pix.
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
Definition eq s s' : Prop :=
  pix.Equal (screen_state s) (screen_state s').

Lemma eq_refl : forall s, eq s s.
Proof.
  intros.
  unfold eq.
  destruct s.
  simpl.
  constructor.
Qed.

Lemma eq_sym : forall x y , eq x y -> eq y x.
Proof.
  unfold eq. unfold pix.Equal.
  intros.
  auto.
Qed.


Lemma eq_trans : forall x y z , eq x y -> eq y z -> eq x z.
Proof.
  unfold eq.
  intros; simpl.
  destruct x, y, z.
  unfold pix.Equal in *.
  intros.
  rewrite H.
  rewrite H0.
  auto.
Qed.

Definition draw_pixel := (fun s p c => mkPState (update p c (screen_state s)) (screen_size s)).


Lemma  pix_ok : forall (p1 p2 : point) (c1 c2 : color) t,
             p1 <> p2 ->
             eq (draw_pixel (draw_pixel t p2 c1) p1 c2)
               (draw_pixel (draw_pixel t p1 c2) p2 c1).
Proof.
  intros.
  unfold eq.
  simpl.
  unfold update.
  unfold pix.Equal.
  intros .
  do 4 rewrite pix_prop.F.add_o.
  unfold not in H.
  case_eq (pix.E.eq_dec p2 y);
    case_eq (pix.E.eq_dec p1 y); auto.
  intros.
  destruct a, a0.
  destruct p1,p2,y.
  simpl in *.
  subst.
  destruct H; auto.
Qed.

Instance pixelMap_graphics_prims : graphics_prims pixelState :=
  mkGraphicsPrims pixelState
    (init)
    (fun s p => mkPState (screen_state s) p)
    draw_pixel
    eq
    eq_refl
    eq_sym
    eq_trans
    pix_ok.

Open Scope Z_scope.
Definition prog1 : g_com :=
   lineto (1,2) (1,20) Red.
  (* draw_rect (1,2) (3,4) Red. *)


Fixpoint toListPair (l : list (pix.key * color)) : list (pix.key):=
  match l with
  | nil => nil
  | cons (h, c) t => cons h (toListPair t)
  end.

Definition hi := (pix.elements (screen_state (interp (init_state tt) prog1))).
