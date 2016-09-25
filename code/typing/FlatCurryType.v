Require Import CQE.FlatCurry CQE.Maps CQE.Basics.
Require Import Datatypes EqNat Lists.List Ascii Bool String Program.Basics.
Import ListNotations.
Local Open Scope nat_scope.

Section Context.

  (* A context maps variable IDs to types and contains the full type and
     a list of type variables for functions and constructors. *)
  Inductive context : Type := 
    | Con : (partial_map VarIndex TypeExpr) ->
            (partial_map QName (TypeExpr * (list TVarIndex))) ->
            (partial_map QName (TypeExpr * (list TVarIndex))) -> context.

  (* Empty context *)
  Definition empty := Con emptymap emptymap emptymap.

  (* Returns variable context of a context. *)
  Definition vCon (c : context) := match c with Con vcon _ _ => vcon end.

  (* Returns function context of a context. *)
  Definition fCon (c : context) := match c with Con _ fcon _ => fcon end.

  (* Returns constructor context of a context. *)
  Definition cCon (c : context) := match c with Con _ _ ccon => ccon end.

    (* Returns the appropriate context depending on a CombType. *)
  Definition combCon (ct : CombType) (c : context) :=
    match ct with
    | FuncCall       => fCon c
    | FuncPartCall _ => fCon c
    | ConsCall       => cCon c
    | ConsPartCall _ => cCon c
    end.

  Definition partCombArgs (ct : CombType) : nat :=
  match ct with
  | FuncPartCall n => n
  | ConsPartCall n => n
  | _              => 0
  end.

  (* Boolean equality of QNames *)
  Definition beq_qname (q : QName) (q' : QName) : bool :=
    match q, q' with
    | (n, m), (n', m') => (andb (beq_str n n') (beq_str m m'))
    end.

  (* Updates a variable's type in a context. *)
  Definition varUpdate Gamma (vi : VarIndex) (t : TypeExpr) : context := 
    Con (update beq_nat (vCon Gamma) vi t) (fCon Gamma) (cCon Gamma).

  (* Updates the function entry of a QName. *)
  Definition funcUpdate Gamma (qn : QName) (tvis : (TypeExpr * list TVarIndex)) : context :=
    Con (vCon Gamma) (update beq_qname (fCon Gamma) qn tvis) (cCon Gamma).

  (* Updates the constructor entry of a QName. *)
  Definition consUpdate Gamma (qn : QName) (tvis : (TypeExpr * list TVarIndex)) : context :=
    Con (vCon Gamma) (fCon Gamma) (update beq_qname (cCon Gamma) qn tvis).

End Context.

Section ProgToContext.

  (* Takes a list of types and returns a corresponding function type. *)
  Fixpoint tyListFunc (tys : list TypeExpr) : TypeExpr :=
    match tys with
    | [t]     => t
    | t :: ts => FuncType t (tyListFunc ts)
    | []      => TCons ("Coq","NoType") []
    end.

  (* Adds a constructor to a context. Because we need the full type, the
     constructor's argument types and the type of constructor are combined
     to a function type, the second component of the pair is a list of the
     type variables.
     Example: (Just a) has the entry (a -> Maybe a, [a]) in the context. *)
  Definition addCons Gamma (tqn : QName) (vis : list TVarIndex) (c : ConsDecl) : context :=
    match c with
    | Cons qn _ _ args => let ty := (args ++ [TCons tqn (map TVar vis)])
                           in consUpdate Gamma qn (tyListFunc ty, vis)
    end.

  (* Adds multiple constructors to a context. *)
  Fixpoint addConsL Gamma (tqn : QName) (vis : list TVarIndex) (cs : list ConsDecl) : context :=
    match cs with
    | [] => Gamma
    | c :: cs => addConsL (addCons Gamma tqn vis c) tqn vis cs
    end.

  (* Extracts constructor entries from type declarations. *)
  Fixpoint parseTypes Gamma (tydecls : list TypeDecl) : context :=
    match tydecls with
    | (Typec qn _ vis cs) :: tydecls => parseTypes (addConsL Gamma qn vis cs) tydecls
    | _ => Gamma
    end.

  (* Extracts indices of type variables from a type, with possibily
     multiple entries for the same variable. *)
  Fixpoint extractTVars (t : TypeExpr) : list TVarIndex :=
    match t with
    | TVar i      => [i]
    | TCons _ tys => concat (map extractTVars tys)
    | FuncType argT retT => (extractTVars argT) ++ (extractTVars retT)
    end.

  (* Removes duplicates from a list of type variable indices.
     Applying rev before nodup ensures the order is preserved. *)
  Definition funcTVars (t : TypeExpr) : list TVarIndex :=
    rev (Basics.nodup beq_nat (rev (extractTVars t))).

  (* Adds a function entry to a context. *)
  Fixpoint addFunc Gamma (fdecl : FuncDecl) : context :=
    match fdecl with
    | Func qn _ _ ty _ => funcUpdate Gamma qn (ty, funcTVars ty)
    end.

  (* Adds multiple functions to a context. *)
  Definition parseFuncs Gamma (fdecls : list FuncDecl) : context :=
    fold_right (fun f c => addFunc c f) Gamma fdecls.

  (* Adds function and constructor entries to a context. *)
  Definition parseProgram (p : TProg) : context :=
    match p with
    | Prog _ _ tydecls funcdecls _ => parseFuncs (parseTypes empty tydecls) funcdecls
    end.

End ProgToContext.

Section TypingHelper.

  (* Takes a function type and and an optional nat. If there is none supplied,
     the last type of the function (e.g. c for a -> b -> c) is returned. For 
     some number n, the first n types get removed, e.g. a -> b; Some 0 => a -> b,
     a -> b -> c; Some 1 => b -> c, ... *)
  Fixpoint funcPart (t : TypeExpr) (n : option nat) : TypeExpr :=
    match t with
    | TVar _    as t => t
    | TCons _ _ as c => c
    | FuncType _ (FuncType _ _ as f') as f => match n with
                                              | None       => funcPart f' None
                                              | Some O     => f
                                              | Some (S n) => funcPart f' (Some n)
                                              end
    | FuncType _ retT     as f => match n with
                                              | Some O => f
                                              | _      => retT
                                              end
    end.

  (* Adds multiple variable -> type entries to a context. *)
  Definition multiTypeUpdate Gamma (vitys : list (VarIndex * TypeExpr)) : context :=
    fold_right (fun vity con => match vity with (vi, ty) => varUpdate con vi ty end)
               Gamma vitys.

  (* Adds list of multiple variable -> type entries to a context. *)
  Definition multiListTypeUpdate Gamma (vityls : list ((list VarIndex) * (list TypeExpr))) : context :=
    fold_right (fun vityl con => match vityl with
                                 | (vil, tyl) => multiTypeUpdate Gamma (zip vil tyl)
                                 end)
               Gamma vityls.

  (* Returns type of a literal. *)
  Definition litType (l : Literal) : TypeExpr :=
    match l with
    | Intc _   => Int
    | Floatc _ => Float
    | Charc _  => Char
    end.

  (* Returns expressions of a list of branch expressions. *)
  Definition brexprsToExprs (brexprs : list BranchExpr) : list Expr :=
    map (fun brexpr => match brexpr with (Branch _ e) => e end) brexprs.

  (* Returns patterns of a list of branch expressions. *)
  Definition brexprsToPatterns (brexprs : list BranchExpr) : list TPattern :=
    map (fun brexpr => match brexpr with (Branch p _) => p end) brexprs.

  (* Splits a pattern into a pair the QName and a list of type variables. *)
  Definition pattSplit (p : TPattern) : (QName * list VarIndex) :=
    match p with 
    | (Pattern qn vis)      => (qn,vis)
    | (LPattern (Intc n))   => (("Prelude","Int"), [])
    | (LPattern (Charc c))  => (("Prelude","Char"), [])
    | (LPattern (Floatc f)) => (("Prelude","Float"), [])
    end.

  (* Replaces the second element of every pair in a list. *)
  Fixpoint replaceSnd {A B C : Type} (abs : list (A * B)) (cs : list C) : list (A * C) :=
    match abs, cs with
    | ((a, b) :: abs), (c :: cs) => (a, c) :: (replaceSnd abs cs)
    | _, _                       => []
    end.

  (* Substitues a type variable k with a replacement type t  in a type t'. *)
  Fixpoint typeSubst (k: TVarIndex) (t: TypeExpr) (t': TypeExpr) : TypeExpr :=
    match t' with
    | TVar i as v  => if (beq_nat i k) then t else v
    | FuncType argT retT => FuncType (typeSubst k t argT) (typeSubst k t retT)
    | TCons qn ts => TCons qn (map (typeSubst k t) ts)
    end.

  (* Substitutes multiple type variables with multiple replacement types in a type. *)
  Definition multiTypeSubst (ks : list TVarIndex) (ts : list TypeExpr) (t' : TypeExpr) : TypeExpr :=
    fold_right (fun kt t' => match kt with (k, t) => typeSubst k t t' end)
               t' (zip ks ts).

  (* Returns the number of arguments a function has. *)
  Fixpoint funcArgCnt (f : TypeExpr) : nat :=
    match f with
    | FuncType _ (FuncType _ _ as f') => 1 + funcArgCnt f'
    | FuncType _ _ => 1
    | _ => 0
    end.

  (* Default values for failed computations. *)
  Definition noType := TCons ("Coq", "NoType") [].
  Definition failType := (noType, @nil TVarIndex).


  Fixpoint funcTyList' (l : TypeExpr) : (list TypeExpr * TypeExpr) :=
    match l with
    | FuncType (FuncType _ _ as f) retT => let (x,y) := (funcTyList' retT) in ([f] ++ x, y)
    | FuncType argT (FuncType _ _ as retT) => let (x,y) := (funcTyList' argT) in
                                              let (a,b) := (funcTyList' retT) in (x ++ a, b)
    | FuncType argT retT => let (x,y) := (funcTyList' argT) in (x, retT)
    | tyexpr => ([tyexpr], tyexpr)
    end.

  (* Takes a function type and returns a pair of the function's argument types
     and the return type. Example: a -> b -> Int => ([a,b],Int) *)
  Fixpoint funcTyList (l : TypeExpr) : (list TypeExpr * TypeExpr) :=
    match l with
    | FuncType _ _ as f => funcTyList' f
    | tyexpr => ([], tyexpr)
    end.

End TypingHelper.

Section Typing.

  (* Rules for the specialization of types *)
  Reserved Notation "t '==>' t1" (at level 40).
  Inductive isSpecializableTo : TypeExpr -> TypeExpr -> Prop :=
    | T_Eq   : forall T, T  ==> T
    | T_Spec : forall T T' substTypes,
                 multiTypeSubst (funcTVars T') substTypes T' = T ->
                 T' ==> T
  where "t '==>' t1" := (isSpecializableTo t t1).

  (* Typing rules *)
  Definition length := Datatypes.length.
  Reserved Notation "Gamma '|-' t ':::' T" (at level 40).
  Inductive hasType : context -> Expr -> TypeExpr -> Prop :=
    | T_Var :       forall Gamma vi T,
                      (vCon Gamma) vi = Some T ->
                      Gamma |- (Var vi) ::: T

    | T_Lit :       forall Gamma l T,
                      T = litType l ->
                      Gamma |- (Lit l) ::: T

    | T_Comb :      forall Gamma qname exprs cType substTypes T,
                      let funcT := fromOption failType ((combCon cType Gamma) qname) in
                      let specT := multiTypeSubst (snd funcT) substTypes (fst funcT)
                       in funcPart specT None = T ->
                          Forall2 (hasType Gamma) exprs (fst (funcTyList specT)) ->
                      Gamma |- (Comb cType qname exprs) ::: T

    | T_Comb_Part : forall Gamma qname exprs substTypes cType T,
                      let funcT := fromOption failType ((combCon cType Gamma) qname) in
                      let specT := multiTypeSubst (snd funcT) substTypes (fst funcT) in
                      let     k := funcArgCnt (fst funcT) - (partCombArgs cType) in
                      let argTs := firstn (@length Expr exprs) (fst (funcTyList specT))
                       in funcPart specT (Some k) = T ->
                          Forall2 (hasType Gamma) exprs argTs ->
                      Gamma |- (Comb cType qname exprs) ::: T

    | T_Let :       forall Gamma ve ves tyexprs e T,
                      let vexprs   := (ve :: ves) in
                      let exprs    := map snd vexprs in
                      let vtyexprs := replaceSnd vexprs tyexprs in
                      let Delta    := multiTypeUpdate Gamma vtyexprs
                       in Forall2 (hasType Delta) exprs tyexprs ->
                          Delta |- e ::: T ->
                      Gamma |- (Let (ve :: ves) e) ::: T

    | T_Free :      forall Gamma vis expr tyexprs T,
                      let Omega := multiTypeUpdate Gamma (zip vis tyexprs)
                       in Omega |- expr ::: T ->
                      Gamma |- (Free vis expr) ::: T

    | T_Or :        forall Gamma e1 e2 T,
                      Gamma |- e1 ::: T ->
                      Gamma |- e2 ::: T ->
                      Gamma |- (Or e1 e2) ::: T

    | T_Case :      forall Gamma ctype e substTypes T Tc p vis brexprs',
                      let  brexprs := Branch p vis :: brexprs' in
                      let   pattps := (map pattSplit (brexprsToPatterns brexprs)) in
                      let contyvis := map (compose (fromOption failType) (cCon Gamma))
                                          (map fst pattps) in
                      let     tvis := snd (fromOption failType (cCon Gamma (fst (pattSplit p)))) in
                      let   specTs := map (multiTypeSubst tvis substTypes)
                                          (map fst contyvis) in
                      let  vistysl := zip (map snd pattps)
                                          (map (compose fst funcTyList) specTs) in
                      let    Delta := multiListTypeUpdate Gamma vistysl
                       in Forall (flip (hasType Delta) T) (brexprsToExprs brexprs) ->
                          Forall (fun ty => ty = Tc) (map ((flip funcPart) None) specTs) ->
                      Gamma |- e ::: Tc ->
                      Gamma |- (Case ctype e (Branch p vis :: brexprs')) ::: T

    | T_Typed :     forall Gamma e t T,
                      Gamma |- e ::: T ->
                      T ==> t ->
                      Gamma |- (Typed e t) ::: t

  where "Gamma '|-' t ':::' T" := (hasType Gamma t T).

End Typing.

Module TypingNotation.
  Notation "Gamma '|-' t ':::' T" := (hasType Gamma t T) (at level 40) : typing_scope.
End TypingNotation.

Import TypingNotation.
Open Scope typing_scope.
Section Examples.
  Definition con := parseProgram 
   (Prog "test"
  ["Prelude"]
  [
  (Typec ("test","Maybe") Public  [0]  [(Cons ("test","Just") 1 Public  [(TVar 0)] );(Cons ("test","Nothing") 0 Public  [] )] );
  (Typec ("test","Test") Public  [0;1]  [(Cons ("test","T") 4 Public  [(TCons ("Prelude","Int") [] );(TVar 0);(TCons ("Prelude","Char") [] );(TVar 1)] )] )
  ]
  [
  (Func ("test","first") 3  Public 
        (FuncType (TVar 0) (FuncType (TCons ("Prelude","Int") [] ) (FuncType (TVar 1) (TVar 0))))
        (Rule  [1;2;3] (Var 1)));
  (Func ("test","left") 2  Public 
        (FuncType (TVar 0) (FuncType (TVar 1) (TVar 0)))
        (Rule  [1;2] (Var 1)));
  (Func ("test","plus") 2  Public 
        (FuncType (TCons ("Prelude","Int") [] ) (FuncType (TCons ("Prelude","Int") [] ) (TCons ("Prelude","Int") [] )))
        (Rule  [1;2] (Comb FuncCall ("Prelude","+") [(Var 1);(Var 2)] )));
  (Func ("test","test_case") 1  Public 
        (FuncType (TCons ("Prelude","Maybe") [(TCons ("Prelude","Int") [] )] ) (TCons ("Prelude","Int") [] ))
        (Rule  [1] (Case Rigid (Var 1) [(Branch (Pattern ("Prelude","Just") [2] )(Var 2));(Branch (Pattern ("Prelude","Nothing") [] )(Lit (Intc 5)))] )));
  (Func ("test","id") 1  Public 
        (FuncType (TVar 0) (TVar 0))
        (Rule  [1] (Var 1)))
  ]
  [] 
  ).

  Example e0 : con |- (Comb (FuncPartCall 2) ("test","first") [(Lit (Charc "a"))] ) ::: FuncType Int (FuncType (TVar 1) Char).
  Proof.
    apply T_Comb_Part with (substTypes := [Char]).
    simpl.
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Example e1 : con |- Comb FuncCall ("test","left") [(Lit (Intc 1));(Lit (Charc "a"))] ::: Int.
  Proof. apply T_Comb with (substTypes := [Int; Char]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition letexp := Let  [(1,(Comb FuncCall ("test","plus") [(Lit (Intc 3));(Lit (Intc 2))] ))] (Comb FuncCall ("test","plus") [(Var 1);(Lit (Intc 4))]).
  Example e2 : con |- letexp ::: Int.
  Proof. apply T_Let with (tyexprs := [Int]).
    apply Forall2_cons. apply T_Comb with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
    apply Forall2_nil.
    apply T_Comb with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition letexp2 := Let  [(1,(Comb FuncCall ("test","plus") [(Var 2);(Lit (Intc 1))] ));(2,(Comb FuncCall ("test","plus") [(Var 1);(Lit (Intc 2))] ))] (Comb FuncCall ("test","plus") [(Var 1);(Lit (Intc 3))] ).
  Example e3 : con |- letexp2 ::: Int.
  Proof.
    apply T_Let with (tyexprs := [Int; Int]).
    apply Forall2_cons. apply T_Comb with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
    apply Forall2_cons. simpl. apply T_Comb with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
    apply Forall2_nil.
    simpl. apply T_Comb with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition letexp3 := Let  [(1,(Comb FuncCall ("test","plus") [(Lit (Intc 1));(Lit (Intc 1))] ));(2,(Comb FuncCall ("test","plus") [(Var 1);(Lit (Intc 1))] ))] (Comb FuncCall ("test","plus") [(Var 2);(Var 1)] ).
  Example e4 : con |- letexp3 ::: Int.
  Proof. apply T_Let with (tyexprs := [Int; Int]).
    apply Forall2_cons. apply T_Comb with (substTypes := []).
    simpl. intros.
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
    apply Forall2_cons. apply T_Comb with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
    apply Forall2_nil.
    simpl. apply T_Comb with (substTypes := []).
    reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_cons. apply T_Var. reflexivity.
    apply Forall2_nil.
Qed.

  Definition comb1 := (Comb ConsCall ("test","Just") [(Lit (Intc 5))] ).
  Example e5 : con |- comb1 ::: (TCons ("test","Maybe") [Int] ).
  Proof. apply T_Comb with (substTypes := [Int]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition comb2 := Comb ConsCall ("test","T") [Lit (Intc 5); Lit (Intc 2); Lit (Charc "a"); Lit (Charc "b")].
  Example e6 : con |- comb2 ::: (TCons ("test", "Test") [Int; Char]).
  Proof.
    apply T_Comb with (substTypes := [Int; Char]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition comb3 := (Comb (ConsPartCall 1) ("test","T") [(Lit (Intc 5));(Lit (Intc 2));(Lit (Charc "a"))] ).
  Definition e7 : con |- comb3 ::: (FuncType (TVar 1) (TCons ("test","Test") [(TCons ("Prelude","Int") [] );(TVar 1)] )).
  Proof.
    apply T_Comb_Part with (substTypes := [Int]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition free1 := (Free  [1] (Var 1)).
  Example e8 : con |- free1 ::: Int.
  Proof. apply T_Free with (tyexprs := [Int]).
    apply T_Var. reflexivity.
  Qed.

  Definition case1 := (Case Rigid (Var 1) [(Branch (Pattern ("test","Just") [2] )(Var 2));(Branch (Pattern ("test","Nothing") [] )(Lit (Intc 5)))] ).
  Example e9 : (varUpdate con 1 (TCons ("test","Maybe") [Int] )) |- case1 ::: Int.
  Proof.
    apply T_Case with (substTypes := [Int]) (Tc := (TCons ("test","Maybe") [Int] )).
    simpl.
    simpl. apply Forall_cons. apply T_Var. reflexivity.
    apply Forall_cons. apply T_Lit. reflexivity.
    apply Forall_nil.
    simpl. apply Forall_cons. reflexivity.
    apply Forall_cons. reflexivity.
    apply Forall_nil.
    apply T_Var. simpl. reflexivity.
  Qed.

  Example e9a : (varUpdate con 1 (TCons ("test","Maybe") [Int] )) |- case1 ::: Int.
  Proof.
    repeat econstructor;
    try instantiate (1 := [Int]);
    repeat econstructor.
  Qed.

  Definition typed := Typed (Comb (FuncPartCall 1) ("test","id") [] ) (FuncType (TCons ("Prelude","Int") [] ) (TCons ("Prelude","Int") [] )).
  Example e10 : con |- typed ::: FuncType Int Int.
  Proof.
    eapply T_Typed. (* with (T' := FuncType (TVar 0) (TVar 0)). *)
    apply T_Comb_Part with (substTypes := []).
    reflexivity.
    apply Forall2_nil.
    apply T_Spec with (substTypes := [Int]).
    reflexivity.
  Qed.
  
  Definition con2 := parseProgram 
  (Prog "MyProg"
  ["Prelude"]
  [(Typec ("Prelude","Maybe") Public  [0]  
   [(Cons ("Prelude","Just") 1 Public  [(TVar 0)] );(Cons ("Prelude","Nothing") 0 Public  [] )] )]
  [
  (Func ("MyProg","double") 1  Public 
        (FuncType Int Int)
        (Rule  [1] (Comb FuncCall ("Prelude","+") [(Var 1);(Var 1)] )));
  (Func ("MyProg","example1") 0  Public 
        (FuncType (TCons ("Prelude","[]") [Int] ) (TCons ("Prelude","[]") [Int] ))
        (Rule  [] (Comb (FuncPartCall 1) ("Prelude","map") [(Comb (FuncPartCall 1)
        ("MyProg","double") [] )] )));
  (Func ("MyProg","example2") 0  Public 
        (FuncType Bool Bool)
        (Rule  [] (Typed (Comb (FuncPartCall 1) ("Prelude","id") [] )
        (FuncType Bool Bool))));
  (Func ("MyProg","example3") 0  Public 
        (TCons ("Prelude","Int") [] )
        (Rule  [] (Free  [1] (Case Rigid (Var 1) 
        [(Branch (Pattern ("Prelude","Just") [2] )(Var 2));
         (Branch (Pattern ("Prelude","Nothing") [] )(Lit (Intc 0)))] ))));
  (Func ("Prelude","+") 2  Public 
        (FuncType (TCons ("Prelude","Int") [] ) (FuncType (TCons ("Prelude","Int") [] ) (TCons ("Prelude","Int") [] )))
        (Rule  [1;2] (Comb FuncCall ("Prelude","+") [(Var 1);(Var 2)] )));
  (Func ("Prelude","map") 2  Public 
        (FuncType (FuncType (TVar 0) (TVar 1)) (FuncType (TCons ("Prelude","[]") [(TVar 0)] ) (TCons ("Prelude","[]") [(TVar 1)] )))
        (Rule  [1;2] (Case Flex (Var 2) [(Branch (Pattern ("Prelude","[]") [] )(Comb ConsCall ("Prelude","[]") [] ));(Branch (Pattern ("Prelude",":") [3;4] )(Comb ConsCall ("Prelude",":") [(Comb FuncCall ("Prelude","apply") [(Var 1);(Var 3)] );(Comb FuncCall ("Prelude","map") [(Var 1);(Var 4)] )] ))] )));
  (Func ("Prelude","id") 1  Public 
        (FuncType (TVar 0) (TVar 0))
        (Rule  [1] (Var 1)))
  ]
  [] 
  )
  .

  Definition exp1 := (Comb (FuncPartCall 1) ("Prelude","map") [(Comb (FuncPartCall 1)
        ("MyProg","double") [] )] ).
  Definition exp2 := (Typed (Comb (FuncPartCall 1) ("Prelude","id") [] )
        (FuncType Bool Bool)).
  Definition exp3 := (Free  [1] (Case Rigid (Var 1) 
        [(Branch (Pattern ("Prelude","Just") [2] )(Var 2));
         (Branch (Pattern ("Prelude","Nothing") [] )(Lit (Intc 0)))] )).

  Definition example1 : con2 |- exp1 ::: (FuncType (List Int) (List Int)).
  Proof.
    apply T_Comb_Part with (substTypes := [Int; Int]).
      * simpl. reflexivity.
      * apply Forall2_cons.
        - apply T_Comb_Part with (substTypes := []).
          -- reflexivity.
          -- apply Forall2_nil.
        - apply Forall2_nil.
  Qed.

  Definition example2 : con2 |- exp2 ::: FuncType Bool Bool.
  Proof.
    eapply T_Typed.
      * apply T_Comb_Part with (substTypes := []);
        econstructor.
      * apply T_Spec with (substTypes := [Bool]).
        reflexivity.
  Qed.

  Definition example3 : con2 |- exp3 ::: Int.
  Proof.
    apply T_Free with (tyexprs := [TCons ("Prelude", "Maybe") [Int]]).
    apply T_Case with (substTypes := [Int]) (Tc := TCons ("Prelude", "Maybe") [Int]).
      * apply Forall_cons.
        - apply T_Var. reflexivity.
        - apply Forall_cons.
          -- apply T_Lit. reflexivity.
          -- apply Forall_nil.
      * apply Forall_cons.
        - reflexivity.
        - apply Forall_cons.
          -- reflexivity.
          -- apply Forall_nil.
      * apply T_Var. reflexivity.
  Qed.

  Definition example3a : con2 |- exp3 ::: Int.
  Proof.
    apply T_Free with (tyexprs := [TCons ("Prelude", "Maybe") [Int]]).
    eapply T_Case.
      * repeat econstructor. 
        instantiate (1 := [Int]). 
        repeat econstructor.
      * repeat econstructor.
      * repeat econstructor.
  Qed.

  Definition example3b : con2 |- exp3 ::: Int.
  Proof.
    apply T_Free with (tyexprs := [TCons ("Prelude", "Maybe") [Int]]);
    eapply T_Case;
    try instantiate (1 := [Int]);
    (* Show Existentials. *)
    repeat econstructor.
  Qed.

  Definition beq_type (t1 t2 : TypeExpr) := true.
  Fixpoint inferType (c : context) (e : Expr) : TypeExpr :=
    match e with
    | Var i => fromOption noType ((vCon c) i)
    | Lit l => litType l
    | Or e1 e2 => let type1 := (inferType c e1) in
                  let type2 := (inferType c e2)
                   in if (beq_type type1 type2) then type1 else noType
    | _ => noType
    end.

  Theorem typeInference : forall Gamma e, Gamma |- e ::: inferType Gamma e.
  Admitted.

End Examples.