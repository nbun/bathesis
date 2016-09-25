Require Import CQE.FlatCurry EqNat.

Inductive id : Type :=
| Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with Id n1, Id n2 => beq_nat n1 n2 end.

Definition total_map (K V : Type) := K -> V.

Definition partial_map (K V : Type) := total_map K (option V).

Definition tmap_empty {K V : Type} (v : V) : total_map K V := (fun _ => v).

Definition emptymap {K V :Type} : partial_map K V := tmap_empty None.

Definition t_update {K V : Type} (beq : K -> K -> bool) (m : total_map K V) (k : K) (v : V) :=
  fun k' => if beq k k' then v else m k'.

Definition update {K V : Type} (beq : K -> K -> bool) (m : partial_map K V) (k : K) (v : V) :=
  t_update beq m k (Some v).
