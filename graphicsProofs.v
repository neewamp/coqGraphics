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
    | 1 =>  match goal with
                | H : _ \/ _ |- _ => destruct H; auto;
                                     solve_by_inverts 1; try d_all 0
                | _ => intuition; try solve_by_inverts 1
                end
    | 2 => unfold Z.gt,Z.ge,Z.lt,Z.le,not in *  
  end.

Ltac d_and :=
  d_all 0.
Ltac d_or :=
  d_all 1.
Ltac uncomp := 
 d_all 2.
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
| (x1,y1),(x2,y2) => (x1 = x2 /\ y2 <= y1 /\ y1 < y2 + (Z.of_nat h))
end.

Definition on_hline (p1 p2 : point) (w : nat) :=
match p1,p2 with
| (x1,y1),(x2,y2) => (y1 = y2 /\ x2 <= x1 /\ x1 < x2 + (Z.of_nat w))
end.

Definition in_rect (p1 p2 : point) (w h : nat) :=
match p1,p2 with
| (x1,y1),(x2,y2) => (x1 >= x2 /\ y1 >= y2 /\ x1 < x2+Z.of_nat w /\ y1 < y2 + Z.of_nat h)
end.



Notation "a ? b ; c" := ( (a -> b) /\ ((~a) -> c)) (at level 98). 
Notation "s [ p ]" := (pix.find p (screen_state s)) (at level 97).


(* Lemma vline_correct' : forall (p1 p2 :  *)

Print OrderedTypeEx.

Import FMapAVL.
Import FMaps.

Module natcol := FMapAVL.Make Nat_as_OT.
Module natcol_prop := FMapFacts.Properties natcol.


Fixpoint make_num_line (l : natcol.t color ) (x1 n : nat) (c : color) : natcol.t color :=
match n with
| O => l
| S n' => natcol.add (Nat.add x1 n') c (make_num_line l x1 n' c)
end.



Notation "s [ p ]" := (natcol.find p (s)) (at level 97).


Definition on_num_line (x1 x2 n : nat) :=  Nat.le x2 x1 /\ Nat.lt x1 (Nat.add x2 n).

Lemma n_O_not_on_line: forall (x1 x2 : nat), on_num_line x1 x2 0 -> False.
Proof.
intros.
unfold on_num_line in H.
destruct H.
rewrite <- plus_n_O in H0.
unfold Nat.le in H.
unfold Nat.lt in H0.
unfold lt in H0.
d_and.
Qed.

  

Lemma h_O_not_on_vline: forall (x1 x2 y1 y2 : Z), on_vline (x1,y1) (x2,y2) 0 <-> False.
Proof. d_and. Qed.

Lemma w_O_not_on_hline: forall (x1 x2 y1 y2 : Z), on_hline (x1,y1) (x2,y2) 0 <-> False.
Proof. d_and. Qed.




Lemma make_num_line_correct_aux: forall (x1 x2 n : nat), 
   on_num_line x1 x2 (S n) ->
       on_num_line x1 x2 n \/ x1 = Nat.add x2 n.
Proof.
intros.
induction n.
{
  unfold on_num_line in H. 
  d_and.
  unfold Nat.le in H.
  unfold Nat.lt in H0.
  unfold lt in H0.
  right.
  rewrite <- plus_n_O.
  inversion H0.
  {
    rewrite Nat.add_comm in H2.
    simpl in H2.
    apply eq_add_S.
    apply H2.
  }
  d_and.
}
unfold on_num_line in *.
d_and.
unfold Nat.le in *.
unfold Nat.lt in *.
unfold lt in *.
destruct (beq_nat x1 (Nat.add x2 n)) eqn:e.
{
  rewrite beq_nat_true_iff in e.
  subst.
  left.
  split.
  { apply H. }
  rewrite plus_n_Sm.
  auto.
}
rewrite beq_nat_false_iff in e.
unfold not in e.
rewrite <- plus_n_Sm in H0.
rewrite <- plus_n_Sm in H0.
apply Peano.le_S_n in H0.
rewrite <- plus_n_Sm in H2.
inversion H.
{ d_and. }
d_and.
rewrite Nat.le_succ_r in H0.
destruct H0.
{
  left.
  split.
  { d_and. }
  d_and.
}
right.
d_and.
Qed.

Lemma fold_not: forall (T : Type) (t1 t2 : T), (t1 = t2 -> False) <-> t1 <> t2.
Proof. d_and. Qed.


Lemma vline_correct_aux: forall (x1 x2 y1 y2 : Z) (h : nat) ,
  on_vline (x1,y1) (x2,y2) (S h) ->
        on_vline (x1,y1) (x2,y2) h \/ (y1 = y2 + (Z.of_nat h) /\ x1 = x2).
Proof.
d_and.
unfold Z.lt in *.
unfold Z.le in *.
unfold not in *.
destruct (Zeq_bool y1 (y2 + (Z.of_nat h))) eqn:e.
{
  apply Zeq_bool_eq in e.
  d_and.
}
apply Zeq_bool_neq in e.
d_and.

destruct Dcompare with (y1 ?= y2 + Z.of_nat h); d_and.
{
  apply Z.compare_eq in H1.
  d_and.
}
rewrite Zpos_P_of_succ_nat in H0.
apply Zcompare_Gt_not_Lt in H2.
exfalso.
unfold not in H2.
apply H2.
rewrite <- Z.add_assoc.
rewrite Z.add_1_r.
apply H0.
Qed.

Lemma hline_correct_aux: forall (x1 x2 y1 y2 : Z) (w : nat) ,
  on_hline (x1,y1) (x2,y2) (S w) ->
        on_hline (x1,y1) (x2,y2) w \/ (x1 = x2 + (Z.of_nat w) /\ y1 = y2).
Proof.
d_and.
unfold Z.lt in *.
unfold Z.le in *.
unfold not in *.
destruct (Zeq_bool x1 (x2 + (Z.of_nat w))) eqn:e.
{
  apply Zeq_bool_eq in e.
  d_and.
}
apply Zeq_bool_neq in e.
d_and.
destruct Dcompare with (x1 ?= x2 + Z.of_nat w); d_and.
{
  apply Z.compare_eq in H1.
  d_and.
}
rewrite Zpos_P_of_succ_nat in H0.
apply Zcompare_Gt_not_Lt in H2.
exfalso.
unfold not in H2.
apply H2.
rewrite <- Z.add_assoc.
rewrite Z.add_1_r.
apply H0.
Qed.

 
Theorem make_num_line_correct: forall (x1 x2 n : nat) (l : natcol.t color) (c : color), 
                               (on_num_line x1 x2 n) ?
                                            (make_num_line l x2 n c)[x1] = (Some c) ;
                                            (l[x1] = ((make_num_line l x2 n c)[x1])).
Proof.
intros.
induction n.
{
  split.
  {
    intros.
    apply n_O_not_on_line in H.
    inversion H.
  }
  d_and.
}
split.
{
  intros.
  apply make_num_line_correct_aux in H.
  destruct H.
  {
    d_and.
    rewrite <- H2.
    apply natcol_prop.F.add_neq_o.
    d_and.
    unfold on_num_line in *.
    unfold Nat.lt in *.
    unfold lt in *.
    d_and.
  }
  d_and.
  apply natcol_prop.F.add_eq_o.
  auto.
}
d_and.
rewrite H1.
{
  symmetry.
  apply natcol_prop.F.add_neq_o.
  unfold not.
  intros.
  d_and.
  apply H.
  unfold on_num_line.
  split.
  {
      unfold Nat.le.
      apply le_plus_l.
  }
  unfold Nat.lt.
  rewrite <- plus_n_Sm.
  unfold lt.
  constructor.
}
unfold on_num_line in *.
intros.
d_and.
apply H.
rewrite <- plus_n_Sm.
unfold Nat.lt in *.
unfold Nat.le in *.
unfold lt in *.
constructor.
apply H3.
Qed.    


Notation "s [ p ]" := (pix.find p (screen_state s)) (at level 97).




Theorem vline_correct: forall (p1 p2 : point) (h : nat) (c : color) (st : pixelState),
    (on_vline p1 p2 h) ?
                       (draw_vline st p2 c h)[p1] = (Some c);
      st[p1] = ((draw_vline st p2 c h)[p1]).
Proof.
intros.
destruct p1 as (x1,y1).
destruct p2 as (x2,y2).
induction h.
{
  intros.
  split.
  {
   intros.
   rewrite h_O_not_on_vline in H.
   inversion H.
  }
  d_and.
}
intros.
split.
{
  intros.
  apply vline_correct_aux in H.
  destruct H.
  {
    simpl.
    rewrite pix_prop.F.add_neq_o.
    {
      edestruct IHh.
      unfold on_vline in *.
      destruct H.
      d_and.
    }
    d_and.
  }
  d_and.
  apply pix_prop.F.add_eq_o.
  d_and.
}
unfold not.
intros.
simpl.
rewrite pix_prop.F.add_neq_o.
{
  destruct IHh.
  apply H1.
  unfold not.
  intros.
  apply H.
  simpl.
  split.
  { d_and. }
  d_and.
  unfold Z.lt in *.
  unfold Z.le in *.
  apply Zcompare_Lt_trans with (y2 + Z.of_nat h).
  { d_and. }
  rewrite Z.add_compare_mono_l.
  rewrite Zpos_P_of_succ_nat.
  apply Z.lt_succ_diag_r. 
}
d_and.
apply H0.
{ d_and. }
unfold Z.lt.
rewrite Zpos_P_of_succ_nat.
rewrite Z.add_compare_mono_l.
apply Z.lt_succ_diag_r.
Qed.

Theorem hline_correct: forall (p1 p2 : point) (w : nat) (c : color) (st : pixelState),
    (on_hline p1 p2 w) ?
                       (draw_hline st p2 c w)[p1] = (Some c);
      st[p1] = ((draw_hline st p2 c w)[p1]).
Proof.
intros.
destruct p1 as (x1,y1).
destruct p2 as (x2,y2).
induction w.
{
  intros.
  split.
  {
   intros.
   rewrite w_O_not_on_hline in H.
   inversion H.
  }
  d_and.
}
intros.
split.
{
  intros.
  apply hline_correct_aux in H.
  destruct H.
  {
    simpl.
    rewrite pix_prop.F.add_neq_o.
    {
      edestruct IHw.
      unfold on_hline in *.
      destruct H.
      d_and.
    }
    d_and.
  }
  d_and.
  apply pix_prop.F.add_eq_o.
  d_and.
}
unfold not.
intros.
simpl.
rewrite pix_prop.F.add_neq_o.
{
  destruct IHw.
  apply H1.
  unfold not.
  intros.
  apply H.
  simpl.
  split.
  { d_and. }
  d_and. 
  unfold Z.lt in *.
  unfold Z.le in *.
  apply Zcompare_Lt_trans with (x2 + Z.of_nat w).
  { d_and. }
  rewrite Z.add_compare_mono_l.
  rewrite Zpos_P_of_succ_nat.
  apply Z.lt_succ_diag_r. 
}
d_and.
apply H0.
{ d_and. }
unfold Z.lt.
rewrite Zpos_P_of_succ_nat.
rewrite Z.add_compare_mono_l.
apply Z.lt_succ_diag_r.
Qed.


Theorem rect_spec_hline: forall (x1 x2 y1 y2 y : Z) (w h : nat),
               (y2 <= y /\ y < y2 + Z.of_nat h) -> (in_rect (x1,y1) (x2,y2) w h -> on_hline (x1,y) (x2,y) w).
Proof. d_and. Qed.

Theorem fill_rect_h_O: forall (p1 p2 : point) (w : nat),
         (in_rect p1 p2 w 0) -> False.
Proof.
intros.
destruct p1 as [x1 y1].
destruct p2 as [x2 y2].
d_and.
Qed.

Definition in_rect_alt (p1 p2 : point) (w h : nat) :=
match p1,p2 with
| (x1,y1),(x2,y2) => y1 >= y2 /\ y1 < y2 + Z.of_nat h /\ on_hline (x1,y1) (x2,y1) w
end.

Definition in_rect_alt2 (p1 p2 : point) (w h : nat) :=
match p1,p2 with
| (x1,y1),(x2,y2) => x1 >= x2 /\ x1 < x2 + Z.of_nat w /\ on_vline (x1,y1) (x1,y2) h
end.

Theorem rect_def_same: forall (p1 p2 : point) (w h : nat), in_rect_alt p1 p2 w h <-> in_rect p1 p2 w h .
Proof.
intros.
destruct p1 as [x1 y1].
destruct p2 as [x2 y2].
d_and.
Qed.

Theorem rect_def_same2: forall (p1 p2 : point) (w h : nat), in_rect_alt2 p1 p2 w h <-> in_rect p1 p2 w h .
Proof.
intros.
destruct p1 as [x1 y1].
destruct p2 as [x2 y2].
d_and.
Qed.

  
Lemma fill_rect_correct_aux: forall (x1 y1 x2 y2 : Z) (w h : nat), 
      in_rect (x1,y1) (x2,y2) w h <-> on_hline (x1,y2) (x2,y2) w /\ on_vline (x2,y1) (x2,y2) h.
Proof. d_and. Qed.


Theorem fill_rect_correct: forall (p1 p2 : point) (w h : nat) (c : color) (st : pixelState),
        (in_rect p1 p2 w h) ?
        (fill_rect_rc st p2 w h c)[p1] = Some c ;
        (fill_rect_rc st p2 w h c)[p1] = (st[p1]).
Proof.
destruct p1 as [x1 y1].
destruct p2 as [x2 y2].
intros.
induction h.
{
  rewrite fill_rect_correct_aux.
  split.
  {
    intros.
    destruct H.
    apply h_O_not_on_vline in H0.
    inversion H0.
  }
  d_and.
}
rewrite fill_rect_correct_aux.
split.
{
  intros.
  destruct H.
  simpl.
  apply vline_correct_aux in H0.
  destruct H0.
  {
    edestruct hline_correct.    
    rewrite <- H2.
    { d_and. }
    d_and.
  }
  edestruct hline_correct.
  rewrite H1.
  { d_and. }
  d_and.
}
unfold not.
intros.
simpl.
destruct IHh.
edestruct hline_correct.
rewrite <- H3.
{
  rewrite H1.
  { auto. }
  unfold not.
  rewrite fill_rect_correct_aux.
  intros.
  destruct H4.
  apply H.
  split.
  { apply H4. }
  simpl.
  simpl in H5.
  destruct H5.
  destruct H6.
  split.
  { auto. }
  split.
  { apply H6. }
  rewrite Zpos_P_of_succ_nat.
  eapply Z.lt_trans.
  { apply H7. }
  unfold Z.lt.
  rewrite Z.add_compare_mono_l.
  apply Z.lt_succ_diag_r.
}
unfold not.
intros.
 apply H.
split.
{ d_and. }
simpl.
split.
{ auto. }
simpl in H4.
destruct H4.
destruct H5.
split.
{ d_and. }
subst.
unfold  Z.lt.
rewrite Z.add_compare_mono_l.
rewrite Zpos_P_of_succ_nat.
apply Z.lt_succ_diag_r.
Qed.
  

  
 


Definition in_rect         
         
      
  


