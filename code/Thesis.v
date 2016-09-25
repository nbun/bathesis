Section DataTypes.
  Inductive list (X : Type) : Type :=
    | nil  : list X
    | cons : X -> list X -> list X.

  Check cons nat 8 (nil nat).

  Arguments nil {X}.
  Arguments cons {X} _ _.

  Check cons 8 nil.

  Fail Definition double_cons x y z := (cons x (cons y z)).
  Definition double_cons {A} x y z := (@cons A x (@cons A y z)).

  Check double_cons 2 4 nil.
  Fail Check cons 2 (cons nil nil).

  Definition isEmpty {X : Type} (l : list X) : bool := 
    match l with
    | nil      => true
    | cons _ _ => false
    end.

  Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
    match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
    end.

  Notation "x :: y" := (cons x y) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
  Notation "x ++ y" := (app x y) (at level 60, right associativity).
End DataTypes.

Require Import Datatypes Lists.List.
Import ListNotations.

Section Props.
  Check 1 + 1 = 2.
  Check forall (X : Type) (l : list X), l ++ [] = l.
  Check forall (n : nat), n > 0 -> n * n > 0.
  Check (fun n => n <> 2).

  Example e1 : 1+1=2.
  Proof. simpl. reflexivity. Qed.

  Example e2 : forall (X : Type) (l : list X), [] ++ l = l.
  Proof. intros X l. reflexivity. Qed.

  Example e3 : forall (X : Type) (l : list X), l ++ [] = l.
  Proof. intros X. induction l as [|l ls IH].
    reflexivity.
    simpl. rewrite IH. reflexivity.
  Qed.

  Example e4 : (fun n => n <> 2) 1.
  Proof.
    simpl.
    unfold not.
    intros H.
    inversion H.
  Qed.
Section Props.

Section HigherOrder.
  Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : (list Y) :=
    match l with
    | []     => []
    | h :: t => (f h) :: (map f t)
    end.

  Example e5 : Forall (fun n => n <> 8) [2;4].
  Proof.
    apply Forall_cons. intros H. inversion H.
    apply Forall_cons. intros H. inversion H.
    apply Forall_nil.
  Qed.
End HigherOrder.

Require Import EqNat.

Section IndProp.
  Fixpoint inB (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x' :: l' => if (beq_nat x x') then true else inB x l'
  end.

  Example e6 : inB 42 [1;2;42] = true.
  Proof. reflexivity. Qed.

  Fixpoint In (x : nat) (l : list nat) : Prop :=
    match l with
    | [] => False
    | x' :: l' => x' = x \/ In x l'
    end.

  Example e7 : In 42 [1;2;42].
  Proof.
    simpl. right. right. left.
    reflexivity.
  Qed.

  Inductive inInd : nat -> list nat -> Prop :=
    | head : forall n l, inInd n (n :: l)
    | tail : forall n l e, inInd n l -> inInd n (e :: l).

  Example e8 : inInd 42 [2;42].
  Proof.
    apply tail.
    apply head.
  Qed.

  Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
    | Forall_nil : Forall P [ ]
    | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l ->
                    Forall P (x :: l).

  Check Forall2.

End IndProp.