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
| (x1,y1),(x2,y2) => (x1 = x2 /\ y2 >= y1 /\ y2 < y1 + (Z.of_nat h))
end.


Notation "a ? b ; c" := ( (a -> b) /\ ((~a) -> c)) (at level 98). 
Notation "s [ p ]" := (pix.find p (screen_state s)) (at level 97).


(* Lemma vline_correct' : forall (p1 p2 :  *)

Print OrderedTypeEx.

Import FMapAVL.
Import FMaps.

Module natcol := FMapAVL.Make Nat_as_OT.


Fixpoint make_num_line (l : natcol.t color ) (x1 n : nat) (c : color) : natcol.t color :=
match n with
| O => l
| S n' => natcol.add (Nat.add x1 n') c (make_num_line l x1 n' c)
end.

Notation "s [ p ]" := (natcol.find p (s)) (at level 97).


Definition on_num_line (x1 x2 n : nat) :=  Nat.le x2 x1 /\ Nat.lt x1 (Nat.add x2 n).

Lemma n_O_not_on_line: forall (x1 x2 : nat), on_num_line x1 x2 0 -> False.
intros.
unfold on_num_line in H.
destruct H.
rewrite <- plus_n_O in H0.
unfold Nat.le in H.
unfold Nat.lt in H0.
unfold lt in H0.
d_and.
Qed.  

Lemma make_num_line_correct_aux: forall (x1 x2 n : nat), on_num_line x1 x2 (S n) ->
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
d_and.
{
  apply make_num_line_correct_aux in H1.
  destruct H1.
  {
    d_and.
    unfold on_num_line in *.
    d_and.
    unfold Nat.le in *.
    unfold Nat.lt in *.
    unfold lt in *.
    SearchAbout natcol.add.
    d_and.
    rewrite <- H2.
    
    d_and.
    rewrite <- H0.
    {
      d_and.
  destruct (beq_nat x1 (Nat.add x2 n)) eqn:e.
  {
    rewrite beq_nat_true_iff in e.
    d_and.
    

Theorem vline_correct: forall (p1 p2 : point) (h : nat) (c : color) (st : pixelState),
    (on_vline p1 p2 h) ?
                       (draw_hline st p2 c h)[p1] = (Some c);
      st[p1] = ((draw_hline st p2 c h)[p1]).
  Proof.
    unfold on_vline.
    intros.
    
    destruct p1 as [x1 y1].
    destruct p2 as [x2 y2].
    d_and.
    {
      induction h.
      generalize dependent y1.
      generalize dependent y2.
      {
        d_and.
        rewrite <- Zplus_0_r_reverse in H2.
        uncomp.
        exfalso.
        apply H.
        apply H2.
      }
      uncomp.
      d_and.
      erewrite <- IHh.
      cbv.
      auto.
                
        
        
      

    split.
    {
      intros.
      destruct p1 as [x1 y1].
      destruct p2 as [x2 y2].
      generalize dependent x1.
      generalize dependent x2.
      induction h; intros.
      {
         d_and.         
         rewrite <- Zplus_0_r_reverse in H0.
         unfold Z.ge in H.
         unfold not in H.
         unfold Z.lt in H0.
         assert(HF: False). apply H. apply H0.
         inversion HF.
      }
      d_and.
      destruct IHh with x2 (Z.succ x1).
      {
        split.
        { auto. }
        split.
        {
          unfold Z.ge in *.
          unfold not in *.
          intros.
          unfold Z.lt in *.
        
          
        subst.
            
            
        Focus 2.
        
        
        
        split.
        apply H.
     
        auto.
        split.
      destruct H0.
      unfold Z.ge in H0.
      unfold not in H0.
      unfold Z.lt in H1.
      
                  
         unf
      intros.
    induction h; d_and; subst.
    {
      rewrite <- Zplus_0_r_reverse in H2.
      inversion H2.
      unfold Z.ge in H.
      unfold not in H.
      assert(False). apply H. apply H1.
      inversion H0.
Admitted.

Definition in_rect         
         
      
  


