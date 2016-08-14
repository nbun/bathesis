Require Import CQE.flatCurry CQE.Maps.
Require Import Datatypes EqNat Lists.List Ascii Bool String.
Import ListNotations.
Local Open Scope nat_scope.

Definition func_comp {A B C} (f : B -> C) (g : A -> B) : (A -> C) :=
 (fun x => f (g x)).

(* Takes two lists and returns a list of pairs *)
Fixpoint zip {U V : Type} (us : list U) (vs : list V) : (list (U * V)) :=
match us, vs with
 | [], _  => [] 
 | _ , [] => [] 
 | (u :: us), (v :: vs) => (u, v) :: (zip us vs)
end.

Definition beq_ascii (a : ascii) (b : ascii) : bool :=
  match a, b with
  | Ascii a7 a6 a5 a4 a3 a2 a1 a0 , Ascii b7 b6 b5 b4 b3 b2 b1 b0 =>
     (andb (andb (andb (andb (andb (andb (andb
     (eqb a7 b7)  (eqb a6 b6)) (eqb a5 b5)) (eqb a4 b4)) 
     (eqb a3 b3)) (eqb a2 b2)) (eqb a1 b1)) (eqb a0 b0))
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | S n, O => false
  | S n, S m => ble_nat n m
  end.

Definition bgt_nat (n m : nat) : bool := negb (ble_nat n m).

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

Definition funcTVars (t : TypeExpr) : list TVarIndex := rev (nodup beq_nat (rev (extractTVars t))).


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

Definition multiTypeSubst (ks : list TVarIndex) (ts : list TypeExpr) (t' : TypeExpr) : TypeExpr :=
  fold_right (fun kt t' => match kt with (k, t) => typeSubst k t t' end)
              t' (zip ks ts).

Fixpoint multiListTypeSubst (qns : list QName) (kks : list (list TVarIndex)) (tts : list (list TypeExpr)) (t's : list TypeExpr) : (list TypeExpr) :=
  match kks, tts, t's with
  | ks :: kks, ts :: tts, t' :: t's => (multiTypeSubst ks ts t') :: (multiListTypeSubst qns kks tts t's)
  | _, _, _ => []
  end.

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

Fixpoint varBindings (e : Expr) : list VarIndex :=
  match e with
  | Free vis _ => vis
  | Let viexprs _ => (map fst viexprs)
  | Var _ => []
  | Lit _ => []
  | Comb _ _ es => concat (map varBindings es)
  | Or e1 e2    => (varBindings e1) ++ (varBindings e2)
  | Case _ e _ => varBindings e
  | Typed e _  => varBindings e
  end.

Fixpoint varList (e : Expr) : list VarIndex :=
  match e with
  | Var i as v => [i]
  | Lit _      => []
  | Comb _ _ es => concat (map varList es)
  | Or e1 e2    => (varList e1) ++ (varList e2)
  | Let _ e    => varList e
  | Free _ e   => varList e
  | Case _ e _ => varList e
  | Typed e _  => varList e
  end.

Fixpoint varFree (vbs vs : list VarIndex) : nat :=
  match vs with
  | []      => 0
  | v :: vs => if (elem beq_nat v vbs) then (varFree vbs vs) else 1 + (varFree vbs vs)
  end.

Definition varCount (e : Expr) : nat :=
  varFree ((varBindings e)) ((varList e)).
  
Definition varCountL (es : list Expr) : nat :=
  fold_right Nat.add 0 (map varCount es).

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
                             Forall2 (hasType Gamma) (removelast (funcTyList specT)) exprs ->
                    Gamma |- (Comb FuncCall qname exprs) \in T

  | T_Comb_PFun : forall Gamma qname exprs substTypes remArg T,
                    let funcT := fromOption defaultTyVars ((fCon Gamma) qname) in
                      let specT := multiTypeSubst (snd funcT) substTypes (fst funcT) in
                        let n := funcArgCnt (fst funcT) - remArg
                          in funcPart specT (Some n) = T ->
                             Forall2 (hasType Gamma) (firstn (@length Expr exprs) (funcTyList specT)) exprs ->
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
                             Forall2 (hasType Gamma) (firstn (@length Expr exprs) (funcTyList specT)) exprs ->
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
                  Gamma |- expr \in T ->
                  Forall2 (fun vi tyexpr => (vCon Gamma) vi = Some tyexpr) vis tyexprs ->
                  Gamma |- (Free vis expr) \in T

  | T_Or :        forall Gamma e1 e2 T,
                    Gamma |- e1 \in T ->
                    Gamma |- e2 \in T ->
                    Gamma |- (Or e1 e2) \in T
 (* Wunderschoen... -> TODO: Auslagerung in Funktion *)
  | T_Case :      forall Gamma ctype e brexprs substTypesList T Tc,
                    @length BranchExpr brexprs > 0 ->
                    let pattps := pattsSplit (brexprsToPatterns brexprs) in 
                    let qnames := map fst pattps in
                    let consdecls := map (func_comp (fromOption defaultTyVars) (cCon Gamma)) qnames in
                    let specTs := multiListTypeSubst qnames (map snd consdecls) substTypesList (map fst consdecls) in
                    let vistysl := zip (map snd pattps) (map funcTyList specTs) in
                    let Delta := multiListTypeUpdate Gamma vistysl in
                    Forall (hasType Delta T) (brexprsToExprs brexprs) ->
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
  Example e8 : varUpdate empty 1 Int |- free1 \in Int.
  Proof. apply T_Free with (tyexprs := [Int]).
    apply T_Var. reflexivity.
    simpl. intros. apply Forall2_cons. reflexivity.
    apply Forall2_nil.
  Qed.

  Definition case1 := (Case Rigid (Var 1) [(Branch (Pattern ("test","Just") [2] )(Var 2));(Branch (Pattern ("test","Nothing") [] )(Lit (Intc 5)))] ).
  Example e9 : (varUpdate con 1 Int) |- case1 \in Int.
  Proof.
    apply T_Case with (substTypesList := [[Int]; [Int]]) (Tc := Int).
    simpl. unfold gt. unfold lt. apply le_S. reflexivity.
    simpl. apply Forall_cons. apply T_Var. reflexivity.
    apply Forall_cons. apply T_Lit. reflexivity.
    apply Forall_nil.
    apply T_Var. reflexivity.
  Qed. 
End Examples.

Notation "'Let' v0 := e0 , v1 := e1 'in' e" := (let v0 := e0 in (let v1 := e1 in e)) (at level 0).
Eval compute in Let x := 1, y := 2 in (x + y).
Fail Notation "'Let' v0 := e0 , .. , vn := en 'in' e" := (let v0 := e0 in .. (let vn := en in e) .. ) (at level 0).