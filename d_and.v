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
              | _ => auto; try solve_by_inverts 1; try d_all 1
              end)
    | 1 =>  match goal with
                | H : _ \/ _ |- _ => destruct H; auto;
                                     solve_by_inverts 1; try d_all 0
                | _ => intuition; try solve_by_inverts 1
                end
  end.

Ltac d_and :=
  d_all 0.
Ltac d_or :=
  d_all 1.
Ltac uncomp := 
 d_all 2.
