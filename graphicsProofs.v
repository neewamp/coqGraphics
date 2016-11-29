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
                destruct H; eauto; try solve_by_inverts 1; subst;
                try d_all 0
              | H : exists _, _|- _ => destruct H;
                           try solve_by_inverts 2; auto; try d_all 0
              | H : _ |- ~ _ => unfold not in *; simpl in *;
                                intros; auto; try solve_by_inverts 1;
                                try d_all 0
              | H :~ _ |-  _ => unfold not in H; simpl in *; intros;
                               try solve_by_inverts 1; auto; try d_all 0
              | [H : ?T ?P -> ?Q, H' : ?P |- _ ] => 
                assert (1 = 1);
                   apply H in H'; auto; try d_all 0
              | _ => auto; try solve_by_inverts 1; try d_all 1
              end)
    | S ?n' =>  match goal with
                | H : _ \/ _ |- _ => destruct H; auto;
                                     solve_by_inverts 1; try d_all 0
                | _ => intuition; try solve_by_inverts 1
                end
  end.

Ltac d_and :=
  d_all 0.
Ltac d_or :=
  d_all 1.

Open Scope Z_scope.

Theorem draw_order_pixel: forall (p1 p2 : point) (c1 c2 : color)
    (st : pixelState), p1 <> p2 -> 
    pix.Equal  (screen_state (draw_pixel (draw_pixel st p1 c1) p2 c2))
               (screen_state (draw_pixel (draw_pixel st p2 c2) p1 c1)).
Proof.
  intros.
  simpl.
  unfold update.
  unfold pix.Equal.
  intros .
  do 4 rewrite pix_prop.F.add_o.
  unfold not in H.
  case_eq (pix.E.eq_dec p2 y);
  case_eq (pix.E.eq_dec p1 y);
  d_and.
  destruct p1,p2,y.
  simpl in *.
  subst.
  destruct H; auto.
Qed.


Definition on_vline (p1 p2 : point) (h : nat) :=
match p1,p2 with
| (x1,y1),(x2,y2) => (y1 = y2 /\ x2 >= x1 /\ x2 < x1 + (Z.of_nat h))
end.


Notation "a ? b ; c" := ( (a -> b) /\ ((~a) -> c)) (at level 98). 
Notation "s [ p ]" := (pix.find p (screen_state s)) (at level 97).

(* Lemma vline_correct' : forall (p1 p2 :  *)


Theorem vline_correct: forall (p1 p2 : point) (h : nat) (c : color) (st : pixelState),
    (on_vline p1 p2 h) ?
                       (draw_vline st p2 c h)[p1] = (Some c);
      st[p1] = ((draw_vline st p2 c h)[p1]).
  Proof.
    intros.
    destruct p1,p2.
    unfold on_vline.
    induction h; d_and; subst.
    {
      rewrite <- Zplus_0_r_reverse in H2.
      inversion H2.
      unfold Z.ge in H.
      unfold not in H.
      assert(False). apply H. apply H1.
      inversion H0.
    }
    {
       simpl.         
         
      
  


