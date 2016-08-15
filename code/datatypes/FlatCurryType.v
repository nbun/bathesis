Require Import CQE.FlatCurry CQE.Maps CQE.Basics.
Require Import Datatypes EqNat Lists.List Ascii Bool String Program.Basics.
Import ListNotations.
Local Open Scope nat_scope.

Definition beq_qname (q : QName) (q' : QName) : bool :=
  match q, q' with
  | (n, m), (n', m') => (andb (beq_str n n') (beq_str m m'))
  end.

Inductive context : Type := 
  | Con : (partial_map VarIndex TypeExpr) -> 
          (partial_map QName (TypeExpr * (list TVarIndex))) ->
          (partial_map QName (TypeExpr * (list TVarIndex))) -> context.

Definition empty := Con emptymap emptymap emptymap.

Definition vCon (c : context) := match c with Con vcon _ _ => vcon end.

Definition fCon (c : context) := match c with Con _ fcon _ => fcon end.

Definition cCon (c : context) := match c with Con _ _ ccon => ccon end.

Definition varUpdate (Gamma : context) (vi : VarIndex) (t : TypeExpr) : context := 
  Con (update beq_nat (vCon Gamma) vi t) (fCon Gamma) (cCon Gamma).

Definition funcUpdate (Gamma : context) (qn : QName) (tvis : (TypeExpr * list TVarIndex)) : context :=
  Con (vCon Gamma) (update beq_qname (fCon Gamma) qn tvis) (cCon Gamma).

Definition consUpdate (Gamma : context) (qn : QName) (tvis : (TypeExpr * list TVarIndex)) :=
Con (vCon Gamma) (fCon Gamma) (update beq_qname (cCon Gamma) qn tvis).

Fixpoint tyListFunc (tys : list TypeExpr) : TypeExpr :=
  match tys with
  | [t]     => t
  | t :: ts => FuncType t (tyListFunc ts)
  | []      => TCons ("Coq","NoType") []
  end.

Definition addCons (con : context) (tqn : QName) (vis : list TVarIndex) (c : ConsDecl) : context :=
  match c with
  | Cons qn _ _ args => consUpdate con qn (tyListFunc (args ++ [TCons tqn (map TVar vis)]), vis)
  end.

Fixpoint addConsL (con : context) (tqn : QName) (vis : list TVarIndex) (cs : list ConsDecl) : context :=
  match cs with
  | [] => con
  | c :: cs => addConsL (addCons con tqn vis c) tqn vis cs
  end.

Fixpoint parseTypes (con : context) (tydecls : list TypeDecl) : context :=
  match tydecls with
  | (Typec qn _ vis cs) :: tydecls => parseTypes (addConsL con qn vis cs) tydecls
  | _ => con
  end.

Fixpoint extractTVars (t : TypeExpr) : list TVarIndex :=
  match t with
  | TVar i      => [i]
  | TCons _ tys => concat (map extractTVars tys)
  | FuncType argT retT => (extractTVars argT) ++ (extractTVars retT)
  end.

Definition funcTVars (t : TypeExpr) : list TVarIndex := rev (Basics.nodup beq_nat (rev (extractTVars t))).


Fixpoint addFunc (con : context) (fdecl : FuncDecl) : context :=
  match fdecl with
  | Func qn _ _ ty _ => funcUpdate con qn (ty, funcTVars ty)
  end.

Definition parseFuncs (con : context) (fdecls : list FuncDecl) : context :=
  fold_right (fun f c => addFunc c f) con fdecls.

Definition parseProgram (p : TProg) : context :=
  match p with
  | Prog _ _ tydecls funcdecls _ => parseFuncs (parseTypes empty tydecls) funcdecls
  end.

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
  | FuncType _ retT     as f => match n with
                                            | Some O => f
                                            | _      => retT
                                            end
  end.

Definition multiTypeUpdate (Gamma : context) (vitys : list (VarIndex * TypeExpr)) : context :=
  fold_right (fun vity con => match vity with (vi, ty) => varUpdate con vi ty end)
  Gamma vitys.

Definition multiListTypeUpdate (Gamma : context) (vityls : list ((list VarIndex) * (list TypeExpr))) : context :=
  fold_right (fun vityl con => match vityl with (vil, tyl) => multiTypeUpdate Gamma (zip vil tyl) end)
  Gamma vityls.

Definition litType (l : Literal) : TypeExpr :=
  match l with
  | Intc _   => Int
  | Floatc _ => Float
  | Charc _  => Char
  end.

Definition brexprsToExprs (brexprs : list BranchExpr) : list Expr :=
  map (fun brexpr => match brexpr with (Branch _ e) => e end) brexprs.

Definition brexprsToPatterns (brexprs : list BranchExpr) : list TPattern :=
  map (fun brexpr => match brexpr with (Branch p _) => p end) brexprs.

Fixpoint pattsSplit (ps : list TPattern) : list (QName * (list VarIndex)) :=
  match ps with
  | [] => []
  | (Pattern qn vis) :: ps => (qn,vis) :: (pattsSplit ps)
  | (LPattern l)     :: ps => pattsSplit ps
  end.

Fixpoint replaceSnd {A B C : Type} (abs : list (A * B)) (cs : list C) : list (A * C) :=
  match abs, cs with
  | ((a, b) :: abs), (c :: cs) => (a, c) :: (replaceSnd abs cs)
  | _, _                       => []
  end.

Fixpoint typeSubst (k: TVarIndex) (t: TypeExpr) (t': TypeExpr) : TypeExpr :=
  match t' with
  | TVar i as v  => if (beq_nat i k) then t else v
  | FuncType argT retT => FuncType (typeSubst k t argT) (typeSubst k t retT)
  | TCons qn ts => TCons qn (map (typeSubst k t) ts)
  end.

Definition multiTypeSubst (ks : list TVarIndex) (ts : list TypeExpr) (t' : TypeExpr) : TypeExpr :=
  fold_right (fun kt t' => match kt with (k, t) => typeSubst k t t' end)
              t' (zip ks ts).

Fixpoint funcArgCnt (f : TypeExpr) : nat :=
  match f with
  | FuncType _ (FuncType _ _ as f') => 1 + funcArgCnt f'
  | FuncType _ _ => 1
  | _ => 0
  end.

Definition noType := TCons ("Coq", "NoType") [].
Definition defaultTyVars := (noType, @nil TVarIndex).

Fixpoint funcTyList (l : TypeExpr) : (list TypeExpr * TypeExpr) :=
  match l with
  | FuncType (FuncType _ _ as f) retT => let (x,y) := (funcTyList retT) in ([f] ++ x, y)
  | FuncType argT (FuncType _ _ as retT) => let (x,y) := (funcTyList argT) in
                                              let (a,b) := (funcTyList retT) in (x ++ a, b)
  | FuncType argT retT => let (x,y) := (funcTyList argT) in (x, retT)
  | tyexpr => ([tyexpr], tyexpr)
  end.

Definition length := Datatypes.length.
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
                             Forall2 (hasType Gamma) (fst (funcTyList specT)) exprs ->
                    Gamma |- (Comb FuncCall qname exprs) \in T

  | T_Comb_PFun : forall Gamma qname exprs substTypes remArg T,
                    let funcT := fromOption defaultTyVars ((fCon Gamma) qname) in
                      let specT := multiTypeSubst (snd funcT) substTypes (fst funcT) in
                        let n := funcArgCnt (fst funcT) - remArg
                          in funcPart specT (Some n) = T ->
                             Forall2 (hasType Gamma) (firstn (@length Expr exprs) (fst (funcTyList specT))) exprs ->
                    Gamma |- (Comb (FuncPartCall remArg) qname exprs) \in T

  | T_Comb_Cons : forall Gamma qname exprs substTypes T,
                    let consT := fromOption defaultTyVars ((cCon Gamma) qname) in
                      let specT := multiTypeSubst (snd consT) substTypes (fst consT)
                        in funcPart specT None = T ->
                           Forall2 (hasType Gamma) (fst (funcTyList specT)) exprs ->
                    Gamma |- (Comb ConsCall qname exprs) \in T

  | T_Comb_PCons :forall Gamma qname exprs substTypes remArg T,
                    let consT := fromOption defaultTyVars ((cCon Gamma) qname) in
                      let specT := multiTypeSubst (snd consT) substTypes (fst consT) in
                        let n := funcArgCnt (fst consT) - remArg
                          in funcPart specT (Some n) = T ->
                             Forall2 (hasType Gamma) (firstn (@length Expr exprs) (fst (funcTyList specT))) exprs ->
                    Gamma |- (Comb (ConsPartCall remArg) qname exprs) \in T 

  | T_Let :       forall Gamma vexprs tyexprs e T,
                    @length (VarIndex * Expr) vexprs > 0 ->
                    let exprs := map snd vexprs in
                      let vtyexprs := replaceSnd vexprs tyexprs in
                        let Delta := multiTypeUpdate Gamma vtyexprs
                          in Forall2 (hasType Delta) tyexprs exprs ->
                             Delta |- e \in T ->
                    Gamma |- (Let vexprs e) \in T

  | T_Free :      forall Gamma vis expr tyexprs T,
                  let Omega := multiTypeUpdate Gamma (zip vis tyexprs)
                    in Omega |- expr \in T ->
                  Gamma |- (Free vis expr) \in T

  | T_Or :        forall Gamma e1 e2 T,
                    Gamma |- e1 \in T ->
                    Gamma |- e2 \in T ->
                    Gamma |- (Or e1 e2) \in T
(*
  | T_Case' :      forall Gamma ctype e brexprs substTypes T Tc,
                    @length BranchExpr brexprs > 0 ->
                    let (qns, vis) := unzip (pattsSplit (brexprsToPatterns brexprs)) in
                    let (pattys, pattvis) := unzip (map (compose (fromOption defaultTyVars) (cCon Gamma)) qns) in
                    let specTs  := map (multiTypeSubst (hd [] pattvis) substTypes) pattys in
                    let vistysl := zip vis (map (compose fst funcTyList) specTs) in
                    let Delta := multiListTypeUpdate Gamma vistysl
                    in Forall (hasType Delta T) (brexprsToExprs brexprs) ->
                    Forall (fun ty => ty = Tc) (map ((flip funcPart) None) specTs) ->
                    Gamma |- e \in Tc ->
                    Gamma |- (Case ctype e brexprs) \in T *)
  | T_Case :      forall Gamma ctype e brexprs substTypes T Tc,
                    @length BranchExpr brexprs > 0 ->
                    let pattps   := pattsSplit (brexprsToPatterns brexprs) in
                    let contyvis := map (compose (fromOption defaultTyVars) (cCon Gamma))
                                        (map fst pattps) in
                    let specTs   := map (multiTypeSubst (hd [] (map snd contyvis)) substTypes)
                                        (map fst contyvis) in
                    let vistysl  := zip (map snd pattps)
                                        (map (compose fst funcTyList) specTs) in
                    let Delta    := multiListTypeUpdate Gamma vistysl
                      in Forall (hasType Delta T) (brexprsToExprs brexprs) ->
                         Forall (fun ty => ty = Tc) (map ((flip funcPart) None) specTs) ->
                    Gamma |- e \in Tc ->
                    Gamma |- (Case ctype e brexprs) \in T

  | T_Typed :     forall Gamma e T,
                    Gamma |- e \in T ->
                    Gamma |- (Typed e T) \in T

where "Gamma '|-' t '\in' T" := (hasType Gamma T t).

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
        (Rule  [1] (Case Rigid (Var 1) [(Branch (Pattern ("Prelude","Just") [2] )(Var 2));(Branch (Pattern ("Prelude","Nothing") [] )(Lit (Intc 5)))] )))

  ]
  [] 
  ).

  Example e0 : con |- (Comb (FuncPartCall 2) ("test","first") [(Lit (Charc "a"))] ) \in FuncType Int (FuncType (TVar 1) Char).
  Proof.
    apply T_Comb_PFun with (substTypes := [Char]).
    simpl.
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Example e1 : con |- Comb FuncCall ("test","left") [(Lit (Intc 1));(Lit (Charc "a"))] \in Int.
  Proof. apply T_Comb_Fun with (substTypes := [Int; Char]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition letexp := Let  [(1,(Comb FuncCall ("test","plus") [(Lit (Intc 3));(Lit (Intc 2))] ))] (Comb FuncCall ("test","plus") [(Var 1);(Lit (Intc 4))]).
  Example e2 : con |- letexp \in Int.
  Proof. apply T_Let with (tyexprs := [Int]).
    simpl. unfold gt. unfold lt. reflexivity.
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

  Definition letexp2 := Let  [(1,(Comb FuncCall ("test","plus") [(Var 2);(Lit (Intc 1))] ));(2,(Comb FuncCall ("test","plus") [(Var 1);(Lit (Intc 2))] ))] (Comb FuncCall ("test","plus") [(Var 1);(Lit (Intc 3))] ).
  Example e3 : con |- letexp2 \in Int.
  Proof.
    apply T_Let with (tyexprs := [Int; Int]).
    simpl. unfold gt. unfold lt. apply le_S. reflexivity.
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

  Definition letexp3 := Let  [(1,(Comb FuncCall ("test","plus") [(Lit (Intc 1));(Lit (Intc 1))] ));(2,(Comb FuncCall ("test","plus") [(Var 1);(Lit (Intc 1))] ))] (Comb FuncCall ("test","plus") [(Var 2);(Var 1)] ).
  Example e4 : con |- letexp3 \in Int.
  Proof. apply T_Let with (tyexprs := [Int; Int]).
    simpl. unfold gt. unfold lt. apply le_S. reflexivity.
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

  Definition comb1 := (Comb ConsCall ("test","Just") [(Lit (Intc 5))] ).
  Example e5 : con |- comb1 \in (TCons ("test","Maybe") [Int] ).
  Proof. apply T_Comb_Cons with (substTypes := [Int]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition comb2 := Comb ConsCall ("test","T") [Lit (Intc 5); Lit (Intc 2); Lit (Charc "a"); Lit (Charc "b")].
  Example e6 : con |- comb2 \in (TCons ("test", "Test") [Int; Char]).
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
  Definition e7 : con |- comb3 \in (FuncType (TVar 1) (TCons ("test","Test") [(TCons ("Prelude","Int") [] );(TVar 1)] )).
  Proof.
    apply T_Comb_PCons with (substTypes := [Int]).
    reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_cons. apply T_Lit. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition free1 := (Free  [1] (Var 1)).
  Example e8 : con |- free1 \in Int.
  Proof. apply T_Free with (tyexprs := [Int]).
    apply T_Var. reflexivity.
  Qed.

  Definition case1 := (Case Rigid (Var 1) [(Branch (Pattern ("test","Just") [2] )(Var 2));(Branch (Pattern ("test","Nothing") [] )(Lit (Intc 5)))] ).
  Example e9 : (varUpdate con 1 (TCons ("test","Maybe") [Int] )) |- case1 \in Int.
  Proof.
    apply T_Case with (substTypes := [Int]) (Tc := (TCons ("test","Maybe") [Int] )).
    simpl. unfold gt. unfold lt. apply le_S. reflexivity.
    simpl. apply Forall_cons. apply T_Var. reflexivity.
    apply Forall_cons. apply T_Lit. reflexivity.
    apply Forall_nil.
    simpl. apply Forall_cons. reflexivity.
    apply Forall_cons. reflexivity.
    apply Forall_nil.
    apply T_Var. simpl. reflexivity.
  Qed. 
End Examples.