Require Import Lists.List Ascii Bool String.
Import ListNotations.

(* Takes two lists and returns a list of pairs *)
Fixpoint zip {U V : Type} (us : list U) (vs : list V) : (list (U * V)) :=
match us, vs with
 | [], _  => [] 
 | _ , [] => [] 
 | (u :: us), (v :: vs) => (u, v) :: (zip us vs)
end.

Fixpoint elem {T : Type} (eq : T -> T -> bool) (x : T) (xs : list T) : bool :=
  match xs with
  | [] => false
  | (e :: xs) => if (eq x e) then true else (elem eq x xs)
  end.

Fixpoint nodup {A : Type} (beq : A -> A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if (elem beq x xs) then (nodup beq xs) 
                                  else x :: (nodup beq xs)
  end.

(* Takes a list of option T and returns the Some values. *)
Fixpoint cat_options {T : Type} (l : list (option T)) : list T :=
  match l with
  | []             => []
  | (Some x) :: ls => x :: (cat_options ls)
  |  None    :: ls =>      (cat_options ls)
  end.

Definition beq_ascii (a : ascii) (b : ascii) : bool :=
  match a, b with
  | Ascii a7 a6 a5 a4 a3 a2 a1 a0 , Ascii b7 b6 b5 b4 b3 b2 b1 b0 =>
     (andb (andb (andb (andb (andb (andb (andb
     (eqb a7 b7)  (eqb a6 b6)) (eqb a5 b5)) (eqb a4 b4)) 
     (eqb a3 b3)) (eqb a2 b2)) (eqb a1 b1)) (eqb a0 b0))
  end.

Fixpoint beq_str (s : string) (s' : string) : bool :=
  match s, s' with
  | String c d,  String c' d' => (andb (beq_ascii c c') (beq_str d d'))
  | EmptyString, EmptyString  => true
  | EmptyString, String _ _   => false
  | String _ _ , Emptystring  => false
  end.

Definition fromOption {A : Type} (default : A) (opA : option A) : A :=
  match opA with
  | Some x => x
  | None   => default
  end.