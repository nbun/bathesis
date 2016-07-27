Require Import  Datatypes EqNat Lists.List.
Local Open Scope nat_scope.

Notation " [ ] " := nil (format "[ ]").
Notation " [ x ] " := (cons x nil).
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation " [ x ; y ; .. ; z ] " := (cons x (cons y .. (cons z nil) ..)).

Inductive id : Type :=
  | Id : nat -> id.
  
Definition total_map (A:Type) := id -> A.

Definition partial_map (A:Type) := total_map (option A).

Definition tmap_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).
  

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.
  
Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition emptymap {A:Type} : partial_map A :=
  tmap_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).