Require Import graphicsTypeClass.

Theorem draw_order_pixel: forall (p1 p2 : point) (c1 c2 : color) (st : pix.t color), pix.Equal  (draw_pixel (draw_pixel st p1 c1) p2 c2) (draw_pixel (draw_pixel st p2 c2) p1 c1).
