Require Import CQE.flatCurry CQE.Maps.
Require Import Datatypes EqNat Lists.List Ascii Bool String.
Import ListNotations.
Local Open Scope nat_scope.

Definition beq_ascii (a : ascii) (b : ascii) : bool :=
  match a, b with
  | Ascii a7 a6 a5 a4 a3 a2 a1 a0 , Ascii b7 b6 b5 b4 b3 b2 b1 b0 =>
     (andb (andb (andb (andb (andb (andb (andb
     (eqb a7 b7)  (eqb a6 b6)) (eqb a5 b5)) (eqb a4 b4)) 
     (eqb a3 b3)) (eqb a2 b2)) (eqb a1 b1)) (eqb a0 b0))
  end.

(* Takes two lists and returns a list of pairs *)
Fixpoint zip {U V : Type} (us : list U) (vs : list V) : (list (U * V)) :=
  match us, vs with
   | [], _  => [] 
   | _ , [] => [] 
   | (u :: us), (v :: vs) => (u, v) :: (zip us vs)
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

Inductive context : Type := 
  | Con : (partial_map VarIndex TypeExpr) -> 
          (partial_map QName (TypeExpr * (list TVarIndex))) ->
          (partial_map QName (TypeExpr * (list TVarIndex))) -> context.

Definition vCon (c : context) := match c with Con vcon _ _ => vcon end.

Definition fCon (c : context) := match c with Con _ fcon _ => fcon end.

Definition cCon (c : context) := match c with Con _ _ ccon => ccon end.

Definition varUpdate (Gamma : context) (vi : VarIndex) (t : TypeExpr) : context := 
  Con (update beq_nat (vCon Gamma) vi t) (fCon Gamma) (cCon Gamma).

Definition funcUpdate (Gamma : context) (qn : QName) (tvis : (TypeExpr * list TVarIndex)) : context :=
  Con (vCon Gamma) (update beq_qname (fCon Gamma) qn tvis) (cCon Gamma).

Definition consUpdate (Gamma : context) (qn : QName) (tvis : (TypeExpr * list TVarIndex)) :=
Con (vCon Gamma) (fCon Gamma) (update beq_qname (cCon Gamma) qn tvis).

(* Takes a function type and and an optional nat. If there is none supplied,
   the last type of the function (e.g. c for a -> b -> c) is returned. For 
   some number n, the first n types get removed, e.g. a -> b Some 0 => a -> b,
   a -> b -> c Some 1 => b -> c, ... *)
Fixpoint funcPart (t : TypeExpr) (n : option nat) : TypeExpr :=
  match t with
  | TVar _    as t => t
  | TCons _ _ as c => c
  | FuncType _ (FuncType _ _ as f') as f => match n with
                                            | None       => funcPart f' None
                                            | Some O     => f
                                            | Some (S n) => funcPart f' (Some n)
                                            end
  | FuncType _ (TCons _ _ as c)     as f => match n with
                                            | Some _ => f
                                            | None   => c
                                            end
  | FuncType _ r   => r
  end.

Definition multiTypeUpdate (Gamma : context) (vitys : list (VarIndex * TypeExpr)) :=
  fold_right (fun vity con => match vity with (vi, ty) => varUpdate con vi ty end)
  Gamma vitys.

Definition empty := Con emptymap emptymap emptymap.

Fixpoint elem {T : Type} (eq : T -> T -> bool) (x : T) (xs : list T) : bool :=
  match xs with
  | [] => false
  | (e :: xs) => if (eq x e) then true else (elem eq x xs)
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

Fixpoint replaceSnd {A B C : Type} (abs : list (A * B)) (cs : list C) : list (A * C) :=
  match abs, cs with
  | ((a, b) :: abs), (c :: cs) => (a, c) :: (replaceSnd abs cs)
  | _, _                       => []
  end.

Definition typedeclQname (td : TypeDecl) : QName :=
  match td with 
  | Typec qn _ _ _   => qn
  | TypeSyn qn _ _ _ => qn
  end.

Fixpoint typeSubst (k: TVarIndex) (t: TypeExpr) (t': TypeExpr) : TypeExpr :=
  match t' with
  | TVar i as v  => if (beq_nat i k) then t else v
  | FuncType argT retT => FuncType (typeSubst k t argT) (typeSubst k t retT)
  | TCons qn ts => TCons qn (map (typeSubst k t) ts)
  end.

Fixpoint multiTypeSubst (ks : list TVarIndex) (ts : list TypeExpr) (t' : TypeExpr) : TypeExpr :=
  fold_right (fun kt t' => match kt with (k, t) => typeSubst k t t' end)
              t' (zip ks ts).

Fixpoint specFuncType (ft : TypeExpr) (ts : list TypeExpr) : TypeExpr :=
  match ft, ts with
  | FuncType (TVar i) retT, t :: ts => FuncType t (specFuncType (typeSubst i t retT) ts)
  | FuncType argT     retT, _ :: ts => FuncType argT (specFuncType retT ts)
  | t, _ => t
  end.

Fixpoint funcArgCnt (f : TypeExpr) : nat :=
  match f with
  | FuncType _ (FuncType _ _ as f') => 1 + funcArgCnt f'
  | FuncType _ _ => 1
  | _ => 0
  end.

Definition fromOption {A : Type} (default : A) (opA : option A) : A :=
  match opA with
  | Some x => x
  | None   => default
  end.

Definition defaultTyVars := (TCons ("Coq", "NoType") [], @nil TVarIndex).

Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
 | Forall3_nil  : Forall3 R [] [] []
 | Forall3_cons : forall x y z l l' l'',
    R x y z -> Forall3 R l l' l'' -> Forall3 R (x::l) (y::l') (z:: l'').

Fixpoint funcTyList (l : TypeExpr) : list TypeExpr :=
  match l with
  | FuncType (FuncType _ _ as f) retT => [f] ++ (funcTyList retT)
  | FuncType argT retT => (funcTyList argT) ++ (funcTyList retT)
  | tyexpr => [tyexpr]
  end.
  Eval compute in funcTyList (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TCons ("Prelude", "[]") [TVar 0]) (TCons ("Prelude", "[]")  [TVar 1]))).

Definition length := @Datatypes.length Expr.
Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
Inductive hasType : context -> TypeExpr -> Expr -> Prop :=
  | T_Var :       forall Gamma vi T,
                    (vCon Gamma) vi = Some T ->
                    Gamma |- (Var vi) \in T

  | T_Lit :       forall Gamma l T,
                    T = litType l ->
                    Gamma |- (Lit l) \in T

  | T_Comb_Fun :  forall Gamma qname exprs substTypes T,
                    let funcT := fromOption defaultTyVars ((fCon Gamma) qname) in
                      let specT := multiTypeSubst (snd funcT) substTypes (fst funcT)
                        in funcPart specT None = T ->
                           Forall2 (hasType Gamma) (removelast (funcTyList specT)) exprs ->
                    Gamma |- (Comb FuncCall qname exprs) \in T

  | T_Comb_PFun : forall Gamma qname exprs substTypes remArg T,
                    let funcT := fromOption defaultTyVars ((fCon Gamma) qname) in
                      let specT := multiTypeSubst (snd funcT) substTypes (fst funcT) in
                        let n := funcArgCnt (fst funcT) - remArg
                          in funcPart specT (Some n) = T ->
                             Forall2 (hasType Gamma) (firstn (length exprs) (funcTyList specT)) exprs ->
                    Gamma |- (Comb (FuncPartCall remArg) qname exprs) \in T

  | T_Comb_Cons : forall Gamma qname exprs substTypes T,
                    let consT := fromOption defaultTyVars ((cCon Gamma) qname) in
                      let specT := multiTypeSubst (snd consT) substTypes (fst consT)
                        in funcPart specT None = T ->
                           Forall2 (hasType Gamma) (removelast (funcTyList specT)) exprs ->
                    Gamma |- (Comb ConsCall qname exprs) \in T

  | T_Comb_PCons :forall Gamma qname exprs substTypes remArg T,
                    let consT := fromOption defaultTyVars ((cCon Gamma) qname) in
                      let specT := multiTypeSubst (snd consT) substTypes (fst consT) in
                        let n := funcArgCnt (fst consT) - remArg
                          in funcPart specT (Some n) = T ->
                             Forall2 (hasType Gamma) (firstn (length exprs) (funcTyList specT)) exprs ->
                    Gamma |- (Comb (ConsPartCall remArg) qname exprs) \in T 

  | T_Let :       forall Gamma vexprs tyexprs e T,
                    let exprs := map snd vexprs in
                      let vtyexprs := replaceSnd vexprs tyexprs in
                        let Delta := multiTypeUpdate Gamma vtyexprs
                          in Forall2 (hasType Delta) tyexprs exprs ->
                             Delta |- e \in T ->
                    Gamma |- (Let vexprs e) \in T

  | T_Free :      forall Gamma vis expr tyexprs T,
                  Gamma |- expr \in T ->
                  Forall2 (fun vi tyexpr => (vCon Gamma) vi = Some tyexpr) vis tyexprs ->
                  Gamma |- (Free vis expr) \in T

  | T_Or :        forall Gamma e1 e2 T,
                    Gamma |- e1 \in T ->
                    Gamma |- e2 \in T ->
                    Gamma |- (Or e1 e2) \in T

  | T_Case :      forall Gamma ctype e brexprs T,
                    Forall (hasType Gamma T) (brexprsToExprs brexprs) ->
                    Gamma |- (Case ctype e brexprs) \in T

  | T_Typed :     forall Gamma e T,
                    Gamma |- e \in T ->
                    Gamma |- (Typed e T) \in T

where "Gamma '|-' t '\in' T" := (hasType Gamma T t).

Section Examples.
  Definition con0 := funcUpdate empty ("test","first") (FuncType (TVar 0) (FuncType Int (FuncType (TVar 1) (TVar 0))), [0;1]).
  Example e0 : con0 |- (Comb (FuncPartCall 2) ("test","first") [(Lit (Charc "a"))] ) \in FuncType Int (FuncType (TVar 1) Char).
  Proof.
    apply T_Comb_PFun with (substTypes := [Char]).
    simpl.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition con2 := funcUpdate empty ("test","left") ((FuncType (TVar 0) (FuncType (TVar 1) (TVar 0))), [0;1]).
  Example e1 : con2 |- Comb FuncCall ("test","left") [(Lit (Intc 1));(Lit (Charc "a"))] \in Int.
  Proof. apply T_Comb_Fun with (substTypes := [Int; Char]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition con42 := funcUpdate
                        (funcUpdate 
                          (funcUpdate empty 
                            ("Prelude","map") (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TCons ("Prelude", "[]") [TVar 0]) (TCons ("Prelude", "[]")  [TVar 1])), [0; 1]))
                          ("test", "test") (FuncType (TCons ("Prelude", "[]") [Int]) (TCons ("Prelude", "[]")  [Int]), [0; 1]))
                        ("test", "double") (FuncType Int Int, []).
  Definition func42 := (Comb FuncCall ("Prelude","map") [(Comb (FuncPartCall 1) ("test","double") [] );(Var 1)] ).
  Example e42 : (varUpdate con42 1 (TCons ("Prelude", "[]") [Int])) |- func42 \in (FuncType (TCons ("Prelude", "[]") [Int]) (TCons ("Prelude", "[]")  [Int])).
  Proof. apply T_Comb_Fun with (substTypes := [Int; Int]).
    reflexivity.
    apply Forall2_cons. apply T_Comb_PFun with (substTypes := []).
    simpl. intros.
    apply Forall2_nil.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition letexp := Let  [(1,(Comb FuncCall ("Prelude","+") [(Lit (Intc 3));(Lit (Intc 2))] ))] (Comb FuncCall ("Prelude","+") [(Var 1);(Lit (Intc 4))]).
  Definition con3 := funcUpdate empty ("Prelude","+") (FuncType Int (FuncType Int Int),[]).
  Example e2 : con3 |- letexp \in Int.
  Proof. apply T_Let with (tyexprs := [Int]). 
    apply Forall2_cons. apply T_Comb_Fun with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
    apply Forall2_nil.
    apply T_Comb_Fun with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition letexp2 := Let  [(1,(Comb FuncCall ("Prelude","+") [(Var 2);(Lit (Intc 1))] ));(2,(Comb FuncCall ("Prelude","+") [(Var 1);(Lit (Intc 2))] ))] (Comb FuncCall ("Prelude","+") [(Var 1);(Lit (Intc 3))] ).
  Example e8 : con3 |- letexp2 \in Int.
  Proof.
    apply T_Let with (tyexprs := [Int; Int]).
    apply Forall2_cons. apply T_Comb_Fun with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
    apply Forall2_cons. simpl. apply T_Comb_Fun with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
    apply Forall2_nil.
    simpl. apply T_Comb_Fun with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition letexp3 := Let  [(1,(Comb FuncCall ("Prelude","+") [(Lit (Intc 1));(Lit (Intc 1))] ));(2,(Comb FuncCall ("Prelude","+") [(Var 1);(Lit (Intc 1))] ))] (Comb FuncCall ("Prelude","+") [(Var 2);(Var 1)] ).
  Example e9 : con3 |- letexp3 \in Int.
  Proof. apply T_Let with (tyexprs := [Int; Int]).
  apply Forall2_cons. apply T_Comb_Fun with (substTypes := []).
  simpl. intros.
  reflexivity.
  apply Forall2_cons. apply T_Lit. reflexivity.
  apply Forall2_cons. apply T_Lit. reflexivity.
  apply Forall2_nil.
  apply Forall2_cons. apply T_Comb_Fun with (substTypes := []).
  reflexivity.
  apply Forall2_cons. apply T_Var. reflexivity.
  apply Forall2_cons. apply T_Lit. reflexivity.
  apply Forall2_nil.
  apply Forall2_nil.
  simpl. apply T_Comb_Fun with (substTypes := []).
  reflexivity.
  apply Forall2_cons. apply T_Var. reflexivity.
  apply Forall2_cons. apply T_Var. reflexivity.
  apply Forall2_nil.
Qed. 

  Definition comb1 := (Comb ConsCall ("test","Some") [(Lit (Intc 5))] ).
  Definition typedecl1 := (Typec ("test","Maybe") Public  [0]  [(Cons ("test","None") 0 Public  [] );(Cons ("test","Some") 1 Public  [(TVar 0)] )] ).
  Definition consdecl1 := (Cons ("test","Some") 1 Public  [(TVar 0)] ).

  Example e3 : (consUpdate empty ("test", "Some") (FuncType (TVar 1) (TCons ("test", "Maybe") [TVar 1]), [1])) |- comb1 \in (TCons ("test","Maybe") [Int] ).
  Proof. apply T_Comb_Cons with (substTypes := [Int]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition comb2 := Comb ConsCall ("test","T") [Lit (Intc 5); Lit (Intc 2); Lit (Charc "a"); Lit (Charc "b")].
  Definition con1 := (consUpdate empty ("test","T") ((FuncType Int (FuncType (TVar 0) (FuncType Char (FuncType (TVar 1) (TCons ("test", "Test") [TVar 0; TVar 1]))))), [0; 1])).
  Example e4 : con1 |- comb2 \in (TCons ("test", "Test") [Int; Char]).
  Proof.
    apply T_Comb_Cons with (substTypes := [Int; Char]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition comb3 := (Comb (ConsPartCall 1) ("test","T") [(Lit (Intc 5));(Lit (Intc 2));(Lit (Charc "a"))] ).
  Definition e5 : con1 |- comb3 \in (FuncType (TVar 1) (TCons ("test","Test") [(TCons ("Prelude","Int") [] );(TVar 1)] )).
  Proof.
    apply T_Comb_PCons with (substTypes := [Int; Char]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition free1 := (Free  [1] (Var 1)).
  Example e6 : varUpdate empty 1 Int |- free1 \in Int.
  Proof. apply T_Free with (tyexprs := [Int]).
    apply T_Var. reflexivity.
    simpl. intros. apply Forall2_cons. reflexivity.
    apply Forall2_nil.
  Qed.
End Examples.
