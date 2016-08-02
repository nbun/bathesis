Require Import CQE.flatCurry CQE.Maps.
Require Import Datatypes EqNat Lists.List Ascii Bool String.
Import flatCurry_maps ListNotations.
Local Open Scope nat_scope.

Definition context := (partial_map TypeExpr).

Definition typeCon (c : context) := c.

Definition typeUpdate (Gamma : context) (x : VarIndex) (v : TypeExpr) := 
  (update (typeCon Gamma) x v).

Definition multiTypeUpdate (Gamma : context) (vitys : list (VarIndex * TypeExpr)) :=
  fold_right (fun vity con => match vity with (vi, ty)
                           => typeUpdate con vi ty end)
  Gamma vitys.

Definition empty := @emptymap TypeExpr.

Fixpoint elem {T : Type} (eq : T -> T -> bool) (x : T) (xs : list T) : bool :=
  match xs with
  | [] => false
  | (e :: xs) => if (eq x e) then true else (elem eq x xs)
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

Definition beq_qname (q : QName) (q' : QName) : bool :=
  match q, q' with
  | (n, m), (n', m') => (andb (beq_str n n') (beq_str m m'))
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
  | Prog _ _ _ fds _,  q => 
    find (fun fd => match fd with Func q' _ _ _ _ => (beq_qname q q') end) fds
  end.

Fixpoint searchConsDeclList (q : QName) (cds : list ConsDecl) : option ConsDecl :=
  match q, cds with
  | q, [] => None
  | q, ((Cons q' _ _ _) as cd :: cds) => if (beq_qname q q') then Some cd
                                         else searchConsDeclList q cds
  end.

Fixpoint searchTypeDeclList (q : QName) (tyds : list TypeDecl) : option (ConsDecl * TypeDecl) :=
  match q, tyds with 
  | q, ((Typec _ _ _ cds) as ty :: tyds) => 
    match (searchConsDeclList q cds) with
    | None            => searchTypeDeclList q tyds
    | Some cd => Some (cd, ty)
    end
  | q, ((TypeSyn _ _ _ _) :: tyds) => searchTypeDeclList q tyds
  | q, [] => None
  end.

Definition lookupConsDecl (p : TProg) (q : QName) : option (ConsDecl * TypeDecl) :=
  match p with (Prog _ _ tyds _ _) => searchTypeDeclList q tyds end.


Definition brexprsToExprs (brexprs : list BranchExpr) : list Expr :=
  map (fun brexpr => match brexpr with (Branch _ e) => e end) brexprs.

Fixpoint replSnd {A B C : Type} (abs : list (A * B)) (cs : list C) : list (A * C) :=
  match abs, cs with
  | ((a, b) :: abs), (c :: cs) => (a, c) :: (replSnd abs cs)
  | _, _                       => []
  end.

Definition typedeclQname (td : TypeDecl) : QName :=
  match td with 
  | Typec qn _ _ _   => qn
  | TypeSyn qn _ _ _ => qn
  end.

Definition sndList {A B : Type} (ps : list (A * B)) : list B :=
  map (fun p => match p with (_,b) => b end) ps.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
Inductive hasType : context -> TypeExpr -> Expr -> Prop :=
  | T_Var :       forall Gamma vi T,
                    Gamma vi = Some T ->
                    Gamma |- (Var vi) \in T

  | T_Lit :       forall Gamma l T,
                    T = litType l ->
                    Gamma |- (Lit l) \in T

  | T_Comb_Fun :  forall Gamma P qname exprs fd T,
                    lookupFuncDecl P qname = Some fd ->
                    funcType fd = T ->
                    Gamma |- (Comb FuncCall qname exprs) \in T

  | T_Comb_Cons : forall Gamma P qname tqname exprs tyexprs consdecl typedecl,
                    lookupConsDecl P qname = Some (consdecl, typedecl) ->
                    (forall n,
                      n < Lists.List.length exprs ->
                      Gamma |- (nth n exprs (Lit (Charc "e"))) \in (nth n tyexprs) Char) ->
                      tqname = (typedeclQname typedecl) ->
                    Gamma |- (Comb ConsCall qname exprs) \in (TCons tqname tyexprs)

  | T_Let :       forall Gamma GammaNew vexprs exprs tyexprs vtyexprs e T,
                    exprs = sndList vexprs ->
                    vtyexprs = replSnd vexprs tyexprs ->
                    (forall n,
                      n < Lists.List.length exprs ->
                      Gamma |- (nth n exprs (Lit (Charc "e"))) \in (nth n tyexprs) Char) ->
                    Gamma |- e \in T ->
                    GammaNew = (multiTypeUpdate Gamma vtyexprs) ->
                    GammaNew |- (Let vexprs e) \in T
(*| T_Free : *)
  | T_Or :        forall Gamma e1 e2 T,
                    Gamma |- e1 \in T ->
                    Gamma |- e2 \in T ->
                    Gamma |- (Or e1 e2) \in T
  | T_Case :      forall Gamma ctype e brexprs T,
                    Forall (hasType Gamma T) (brexprsToExprs brexprs) ->
                    Gamma |- (Case ctype e brexprs) \in T
  | T_Typed :     forall Gamma e T,
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
  Proof. apply T_Comb_Fun with (P := prog) (fd := func42).
  reflexivity.
  reflexivity.
  Qed.
  
  Definition letexp := Let [(2,(Comb FuncCall ("Prelude","+") [(Lit (Intc 2));(Lit (Intc 1))] ))] (Comb FuncCall ("Prelude","+") [(Var 1);(Var 2)] ).
  Definition fun2 := (Func ("test","test") 1  Public 
        (FuncType (TCons ("Prelude","Int") [] ) (TCons ("Prelude","Int") [] ))
        (Rule  [1] letexp)).
  Definition plus := Func ("Prelude", "+") 1 Public Int (Rule [1] (Lit (Intc 42))).
  Definition prog2 :=
  (Prog "test"
  ["Prelude"]
  []
  [fun2;plus]
  [] 
  ).
  Example e2 : typeUpdate empty 2 Int |- letexp \in Int.
  Proof. apply T_Let with (Gamma := empty) (exprs := [(Comb FuncCall ("Prelude","+") [(Lit (Intc 2));(Lit (Intc 1))])]) (tyexprs := [Int]) (vtyexprs := [(2,Int)]).
    reflexivity.
    reflexivity.
    simpl. intros. replace n with 0. apply T_Comb_Fun with (P := prog2) (fd := plus).
    reflexivity.
    reflexivity.
    inversion H. reflexivity. inversion H1.
    apply T_Comb_Fun with (P := prog2) (fd := plus).
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.

  Definition comb1 := (Comb ConsCall ("test","Some") [(Lit (Intc 5))] ).
  Definition typedecl1 := (Typec ("test","Maybe") Public  [0]  [(Cons ("test","None") 0 Public  [] );(Cons ("test","Some") 1 Public  [(TVar 0)] )] ).
  Definition consdecl1 := (Cons ("test","Some") 1 Public  [(TVar 0)] ).
  Definition prog3 := 
   (Prog "test"
  ["Prelude"]
  [typedecl1]
  [
  (Func ("test","test") 0  Public 
        (TCons ("test","Maybe") [(TCons ("Prelude","Int") [] )] )
        (Rule  [] (Typed comb1 (TCons ("test","Maybe") [(TCons ("Prelude","Int") [] )] ))))
  ]
  [] 
 ).
 
 Example e3 : empty |- comb1 \in (TCons ("test","Maybe") [(TCons ("Prelude","Int") [] )] ).
 Proof. apply T_Comb_Cons with (P := prog3) (consdecl := consdecl1) (typedecl := typedecl1).
 reflexivity.
 simpl. intros.
 replace n with 0.
 apply T_Lit. reflexivity.
 inversion H. reflexivity. inversion H1.
 reflexivity.
End Examples.

