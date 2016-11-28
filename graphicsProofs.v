Require Export pixelState graphicsTypeClass.
Module pix_prop := FMapFacts.Properties pix.

Open Scope nat_scope.
Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; try reflexivity;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 3.

Set Implicit Arguments.


Ltac d_all n :=
  try intros; repeat subst; auto;
    match n with
    | 0 => (  repeat simpl in *; match goal with
              | H : _/\ _  |- _ =>
                destruct H; eauto; try solve_by_inverts 2; subst;
                try d_all 0
              | H : exists _, _|- _ => destruct H;
                           try solve_by_inverts 2; auto; try d_all 0
              | H : _ |- ~ _ => unfold not in *; simpl in *;
                                intros; auto; try solve_by_inverts 1;
                                try d_all 0
              | H :~ _ |-  _ => unfold not in H; simpl in *; intros;
                               try solve_by_inverts 1; auto; try d_all 0
      
              | _ => auto; try solve_by_inverts 2; try d_all 1
              end)
    | S ?n' =>  match goal with
                | H : _ \/ _ |- _ => destruct H; auto;
                                     solve_by_inverts 2; try d_all 0
                | _ => intuition; try solve_by_inverts 1
                end
  end.

Ltac d_and :=
  d_all 0.
Ltac d_or :=
  d_all 1.

Open Scope positive_scope.




Theorem draw_order_pixel: forall (p1 p2 : point) (c1 c2 : color)
    (st : pixelState),
    pix.Equal  (screen_state (draw_pixel (draw_pixel st p1 c1) p2 c2))
               (screen_state (draw_pixel (draw_pixel st p2 c2) p1 c1)).
Proof.
  intros.
  simpl.
  unfold update.
  unfold pix.Equal.
  intros .
  do 4 rewrite pix_prop.F.add_o.
  case_eq (pix.E.eq_dec p2 y).
  intros.
  destruct a.
  destruct p1, p2.
  



Qed.
