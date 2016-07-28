Require Import CQE.flatCurry.
Require Import Datatypes EqNat Lists.List Ascii Bool String.
Local Open Scope nat_scope.

Notation " [ ] " := nil (format "[ ]").
Notation " [ x ] " := (cons x nil).
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation " [ x ; y ; .. ; z ] " := (cons x (cons y .. (cons z nil) ..)).
  
Definition total_map (A:Type) := VarIndex -> A.

Definition partial_map (A:Type) := total_map (option A).

Definition tmap_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).
  
Definition t_update {A:Type} (m : total_map A)
                    (x : VarIndex) (v : A) :=
  fun x' => if beq_nat x x' then v else m x'.

Definition emptymap {A:Type} : partial_map A :=
  tmap_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : VarIndex) (v : A) :=
  t_update m x (Some v).

Definition context :=  (partial_map TypeExpr).

Definition empty := @emptymap TypeExpr.
Check andb.

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

Definition litType (l : Literal) : TypeExpr :=
  match l with
  | Intc _   => Int
  | Floatc _ => Float
  | Charc _  => Char
  end.

Definition funcType (fd : FuncDecl) : TypeExpr :=
  match fd with Func _ _ _ t _ => t end.

Definition lookupFuncDecl (p : TProg) (q : QName) : option FuncDecl :=
  match p, q with 
  | Prog _ _ _ fds _,  (n, m) => find (fun fd => match fd with Func (n', m') _ _ _ _ => (andb (beq_str n n') (beq_str m m')) end) fds
  end.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Definition brexprsToExprs (brexprs : list BranchExpr) : list Expr :=
  map (fun brexpr => match brexpr with (Branch _ e) => e end) brexprs.

Inductive hasType : context -> TypeExpr -> Expr -> Prop :=
  | T_Var :    forall Gamma i T,
                 Gamma i = Some T ->
                 Gamma |- (Var i) \in T
  | T_Lit :    forall Gamma l T,
                 T = litType l ->
                 Gamma |- (Lit l) \in T
  | T_Comb :   forall Gamma P ctype qname exprs fd T,
                 lookupFuncDecl P qname = Some fd ->
                 funcType fd = T ->
                 (* specialize_func ? *)
                 Gamma |- (Comb ctype qname exprs) \in T
  | T_Let :    forall Gamma vexprs e T,
                 Gamma |- e \in T ->
                 Gamma |- (Let vexprs e) \in T
(*| T_Free : *)
  | T_Or :     forall Gamma e1 e2 T,
                 Gamma |- e1 \in T ->
                 Gamma |- e2 \in T ->
                 Gamma |- (Or e1 e2) \in T
  | T_Case :   forall Gamma ctype e brexprs T,
                 Forall (hasType Gamma T) (brexprsToExprs brexprs) ->
                 Gamma |- (Case ctype e brexprs) \in T
  | T_Typed :  forall Gamma e T,
                 Gamma |- (Typed e T) \in T
where "Gamma '|-' t '\in' T" := (hasType Gamma T t).

Section Examples.
  Definition func42 := 
  (Func ("t","const42") 0  Public (TCons ("Prelude","Int") [] ) (Rule  [] (Lit (Intc 42)))).
  Definition prog := 
  (Prog "t"
  ["Prelude"]
  []
  [func42]
  [] 
  ).
  
  Example e1 : empty |- (Comb FuncCall ("t","const42") []) \in Int.
  Proof. apply T_Comb with (P := prog) (fd := func42).
  reflexivity.
  reflexivity.
  Qed.
End Examples.

