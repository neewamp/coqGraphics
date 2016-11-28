Require Export pixelState graphicsTypeClass.
Module pix_prop := FMapFacts.Properties pix.


Theorem draw_order_pixel: forall (p1 p2 : point) (c1 c2 : color)
    (st : pixelState),
    pix.Equal  (screen_state (draw_pixel (draw_pixel st p1 c1) p2 c2))
               (screen_state (draw_pixel (draw_pixel st p2 c2) p1 c1)).
Proof.
  intros.
  simpl.
  unfold pix.Equal.
  intros.
  unfold update.
  auto.
Qed.
