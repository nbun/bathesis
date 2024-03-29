Require Import CQE.Maps CQE.Basics.
Require Import EqNat Lists.List Program.Basics.
Import ListNotations.

(* Data types *)
Inductive ty : Type :=
  | TVar  : id -> ty
  | TBool : ty
  | TNat  : ty
  | TList : ty -> ty
  | TPair : ty -> ty -> ty
  | TFun  : ty -> ty -> ty.

(* Terms *)
Inductive tm : Type :=
  | tvar   : id -> tm
  | tapp   : tm -> tm -> tm
  | tfun   : id -> list ty -> tm
  | tlet   : id -> tm -> tm -> tm
  | ttrue  : tm
  | tfalse : tm
  | tfail  : ty -> tm
  | tany   : ty -> tm
  | tzero  : tm
  | tsucc  : tm -> tm
  | tadd   : tm -> tm -> tm
  | teqn   : tm -> tm -> tm
  | tpair  : tm -> tm -> tm
  | tnil   : ty -> tm
  | tcons  : tm -> tm -> tm
  | tcaseb : tm -> tm -> tm -> tm
  | tcasep : tm -> id -> id -> tm -> tm
  | tcasel : tm -> id -> id -> tm -> tm -> tm.
(* Tags define the data types a type variable can be specialized to.
   Star-tagged variables can only be specialized to non-functional data types
   while the empty tag allows any specialization. *)
Inductive tag : Type :=
  | tag_star  : tag
  | tag_empty : tag.
  
Section Context.

  (* A context maps IDs of type variables to tags and IDs of variables to 
     types. *)
  Inductive context : Type := 
    | con : (partial_map id tag) -> (partial_map id ty) -> context.

  (* Empty context *)
  Definition empty := con emptymap emptymap.

  (* Returns type context of a context. *)
  Definition type_con (Gamma : context) : (partial_map id ty) :=
    match Gamma with (con _ tyc) => tyc end.

  (* Returns tag context of a context. *)
  Definition tag_con (Gamma : context) : (partial_map id tag) :=
    match Gamma with (con tagc _) => tagc end.

  (* Updates the ID's type in a context. *)
  Definition type_update (Gamma : context) (x : id) (v : ty) := 
    (con (tag_con Gamma) (update beq_id (type_con Gamma) x v)).

  (* Updates the ID's tag in a context. *)
  Definition tag_update (Gamma : context) (x : id) (v : tag) := 
    (con (update beq_id (tag_con Gamma) x v) (type_con Gamma)).

End Context.

Section Functions.

  (* Quantifiers assign tags to IDs of type variables and are used in
     function declarations. *)
  Inductive quantifier : Type :=
    for_all : id -> tag -> quantifier.

  (* Returns ID of a quantifier. *)
  Definition qid (q : quantifier) : id := match q with (for_all id _) => id end.

  (* Returns true if a quantifier has a star tag, false otherwise. *)
  Definition is_star_tagged (q : quantifier) : bool :=
    match q with
    | (for_all _ tag_star)  => true
    | (for_all _ tag_empty) => false
    end.

  (* Function declarations contain all necessary information about a function.
     * the function's name (represented by an ID)
     * a list of quantifiers, which represent the type variables used
     * a (possibly polymorphic) function type
     * a list of IDs, which represent the functions arguments
     * the term that the function evaluates to *)
  Inductive func_decl : Type :=
    FDecl : id -> list quantifier -> ty -> (list id) -> tm -> func_decl.
  Definition default_fd := FDecl (Id 42) [] TNat [] tzero.

  (* Returns a function declaration's list of quantifiers. *)
  Definition fd_qs (fd : func_decl) := match fd with FDecl _ qs _ _ _ => qs end.


  (* Takes function declaration plus a list of types and returns all types
     that have a star-tagged quantifier. *)
  Definition fd_to_star_tys (fd : func_decl) (tys : list ty) : (list ty) :=
    match fd with
    | FDecl _ [] _ _ _ => []
    | FDecl _ qs _ _ _ =>  map snd 
                               (filter (fun qty => match qty with
                                                   | (q,ty) => (is_star_tagged q)
                                                   end)
                                       (zip qs tys))
    end.

  (* Boolean equality between two function declarations. *)
  Definition beq_fd (fd1 fd2 : func_decl) : bool :=
    match fd1, fd2 with
    | (FDecl m _ _ _ _), (FDecl n _ _ _ _) => if (beq_id m n ) 
                                              then true else false
    end.

  (* A program is a list of function declarations. *)
  Definition program := list func_decl.

  (* Takes a program and ID and returns a corresponding function declaration
     if one exists within the program.*)
  Definition lookup_func (p : program) (i : id) : (option func_decl) :=
    find (fun fd => match fd with (FDecl j _ _ _ _) => (beq_id i j) end) p.

  (* Takes an ID and substitutes corresponding type variables with a 
     given type t within a type t'. *)
  Fixpoint ty_subst (k: id) (t: ty) (t': ty) : ty :=
    match t' with
    | TVar i      =>  if (beq_id i k) then t else TVar i
    | TBool       => TBool
    | TNat        => TNat
    | TList T     => TList (ty_subst k t T)
    | TPair TF TS => TPair (ty_subst k t TF) (ty_subst k t TS)
    | TFun  TA TR => TFun  (ty_subst k t TA) (ty_subst k t TR)
    end.

  (* Takes a list of (quantifier,type) pairs and applies a type substitution
     of the quantifier's ID to a type repeatedly to a given type. *)
  Definition multi_ty_subst (qtys : list (quantifier * ty)) (t : ty) : ty := 
    fold_right (fun qty t => match qty with (for_all id _, ty) => ty_subst id ty t end)
               t qtys.

  (* Specializes a function declaration by applying multi_ty_subst with
     a list of concrete types. Returns the specialized type of the function. *)
  Definition specialize_func (fd : func_decl) (tys : list ty) : option ty := 
    match fd with
    | (FDecl _ qs t _ _) => if (beq_nat (length qs) (length tys))
                            then Some (multi_ty_subst (zip qs tys) t)
                            else None
    end.

End Functions.

Section Typing.
  Variable Prog : program.
  (* Rules for being a data type *)
  Reserved Notation "Gamma '|-' T 'in_Data'" (at level 40).
  Inductive is_data_type : context -> ty -> Prop :=
    | D_Var  : forall Gamma n,
                (tag_con Gamma) n  = Some tag_star ->
                Gamma |- (TVar n) in_Data
    | D_Bool : forall Gamma, Gamma |- TBool in_Data
    | D_Nat  : forall Gamma, Gamma |- TNat in_Data
    | D_List : forall Gamma T,
                 Gamma |- T in_Data ->
                 Gamma |- (TList T) in_Data
    | D_Pair : forall Gamma T T', 
                 Gamma |- T in_Data ->
                 Gamma |- T' in_Data ->
                 Gamma |- (TPair T T') in_Data
  where "Gamma '|-' T 'in_Data'" := (is_data_type Gamma T) : typing_scope.

  (* Typing rules *)
  Reserved Notation "Gamma '|-' t ':::' T" (at level 40).
  Inductive has_type : context -> tm -> ty -> Prop :=
    | T_Var :    forall Gamma x T,
                   (type_con Gamma) x = Some T ->
                   Gamma |- tvar x ::: T
    | T_True :   forall Gamma, 
                   Gamma |- ttrue ::: TBool
    | T_False :  forall Gamma,
                   Gamma |- tfalse ::: TBool
    | T_Zero :   forall Gamma,
                   Gamma |- tzero ::: TNat
    | T_Succ :   forall Gamma e,
                   Gamma |- e ::: TNat -> 
                   Gamma |- (tsucc e) ::: TNat
    | T_Nil :    forall Gamma T, 
                   Gamma |- (tnil T) ::: (TList T)
    | T_App :    forall Gamma e1 e2 T1 T2,
                   Gamma |- e1 ::: (TFun T1 T2) ->
                   Gamma |- e2 ::: T1 ->
                   Gamma |- (tapp e1 e2) ::: T2
    | T_Let :    forall Gamma e1 e2 x T1 T2,
                   Gamma |- e1 ::: T1 ->
                   (type_update Gamma x T1) |- e2 ::: T2 ->
                   Gamma |- (tlet x e1 e2) ::: T2
    | T_Fun :    forall Gamma id tys T,
                   let fd := fromOption default_fd (lookup_func Prog id) in 
                   specialize_func fd tys = Some T ->
                   Forall (is_data_type Gamma) (fd_to_star_tys fd tys) ->
                   Gamma |- (tfun id tys) ::: T
    | T_Add :    forall Gamma e1 e2,
                   Gamma |- e1 ::: TNat ->
                   Gamma |- e2 ::: TNat ->
                   Gamma |- (tadd e1 e2) ::: TNat
    | T_EqN :    forall Gamma e1 e2,
                   Gamma |- e1 ::: TNat ->
                   Gamma |- e2 ::: TNat ->
                   Gamma |- (teqn e1 e2) ::: TBool
    | T_Pair:    forall Gamma e1 e2 T1 T2,
                   Gamma |- e1 ::: T1 ->
                   Gamma |- e2 ::: T2 ->
                   Gamma |- (tpair e1 e2) ::: (TPair T1 T2)
    | T_Cons :   forall Gamma e1 e2 T,
                   Gamma |- e1 ::: T ->
                   Gamma |- e2 ::: (TList T) -> 
                   Gamma |- (tcons e1 e2) ::: (TList T)
    | T_CaseL :  forall Gamma e e1 e2 h t T T',
                   Gamma |- e ::: (TList T') ->
                   Gamma |- e1 ::: T ->
                   (type_update 
                     (type_update Gamma h T') t (TList T')) |- e2 ::: T ->
                   Gamma |- (tcasel e h t e1 e2) ::: T
    | T_CaseP :  forall Gamma e e1 l r T T1 T2,
                   Gamma |- e ::: (TPair T1 T2) ->
                   (type_update (type_update Gamma l T1) r T2) |- e1 ::: T ->
                   Gamma |- (tcasep e l r e1) ::: T
    | T_CaseB :  forall Gamma e e1 e2 T,
                   Gamma |- e ::: TBool ->
                   Gamma |- e1 ::: T ->
                   Gamma |- e2 ::: T ->
                   Gamma |- (tcaseb e e1 e2) ::: T
    | T_Fail :   forall Gamma T,
                   Gamma |- (tfail T) ::: T
    | T_Any :    forall Gamma T,
                   Gamma |- T in_Data ->
                   Gamma |- (tany T) ::: T
  where "Gamma '|-' t ':::' T" := (has_type Gamma t T) : typing_scope.
End Typing.

Module TypingNotation.
  Notation "Prog > Gamma '|-' t ':::' T" := (has_type Prog Gamma t T) (at level 40) : typing_scope.
End TypingNotation.

Import TypingNotation.
Open Scope typing_scope.

Section Examples.

  Definition e_prog := @nil func_decl.
  Example t1 : e_prog > empty |- ttrue ::: TBool.
  Proof. apply T_True. Qed.

  Definition c := (type_update empty (Id 5) TNat).

  Example t2 : e_prog > c |- (tvar (Id 5)) ::: TNat.
  Proof. apply T_Var. reflexivity. Qed.

  Example t3 : e_prog > empty |- (tlet (Id 5) tzero 
                                (tadd (tsucc tzero) (tvar (Id 5)))) ::: TNat.
  Proof. 
    apply T_Let with (T1 := TNat).
    * apply T_Zero.
    * apply T_Add.
      - apply T_Succ. apply T_Zero.
      - apply T_Var. reflexivity.
  Qed.

  Example t4 : e_prog > empty |- (tcasel (tnil TNat) (Id 0) (Id 1) (tnil TNat)
                                        (tcons (tsucc tzero) (tnil TNat))) ::: (TList TNat).
  Proof.
    apply T_CaseL with (T' := TNat).
    apply T_Nil.
    apply T_Nil.
    apply T_Cons.
    apply T_Succ. apply T_Zero.
    apply T_Nil.
  Qed.

  Example t5 : e_prog > empty |- 
               (tcasel (tcons ttrue (tnil TBool)) (Id 0) (Id 1) tfalse (tvar (Id 0))) ::: TBool.
  Proof.
    apply T_CaseL with (T' := TBool).
    apply T_Cons.
    apply T_True.
    apply T_Nil.
    apply T_False.
    apply T_Var. reflexivity.
  Qed.

  Definition aContext :=
    type_update 
      (type_update 
        (type_update empty (Id 5) TNat)
        (Id 51) TBool)
      (Id 2) (TVar (Id 1)).

  Example t6 : e_prog > aContext |- tvar (Id 2) ::: TVar (Id 1).
  Proof. apply T_Var. reflexivity. Qed.

  Example multi_t1 : multi_ty_subst 
                     [((for_all (Id 1) tag_empty), TNat);
                      ((for_all (Id 2) tag_empty), (TList TBool))]
                     (TFun (TVar (Id 1)) (TFun (TVar (Id 2)) TNat)) 
                      = (TFun TNat (TFun (TList TBool) TNat)).
  Proof. reflexivity. Qed.

  Example ty_subst1 : ty_subst (Id 1) TBool (TFun (TVar (Id 1)) (TVar (Id 1)))
                      = TFun TBool TBool.
  Proof. reflexivity. Qed.

  Definition prog_fd := FDecl (Id 1) 
                              [(for_all (Id 5) tag_star)] 
                              (TFun (TVar (Id 5)) (TVar (Id 5))) 
                              [Id 1] 
                              (tvar (Id 1)).
  Definition prog2 := [prog_fd].

  Example fun1 : prog2 > aContext |- (tfun (Id 1) [TNat]) ::: (TFun TNat TNat).
  Proof. apply T_Fun.
    reflexivity.
    simpl. apply Forall_cons. apply D_Nat. apply Forall_nil.
  Qed.

  Definition cntxt :=
  tag_update
    (type_update
      (type_update empty (Id 3) TNat)
      (Id 4) TNat)
    (Id 0) tag_star.

  Definition union (t1 t2: tm) : tm := tcaseb (tany TBool) t1 t2.
  Definition fun3 := FDecl (Id 1)
                       [for_all (Id 0) tag_star]
                       (TFun (TVar (Id 0)) (TFun (TVar (Id 0)) (TVar (Id 0))))
                       [Id 42;Id 43]
                       (union (tvar (Id 42)) (tvar (Id 43))).
  Definition prog := [fun3].
  
  Definition app1 := tapp
                      (tapp (tfun (Id 1) [TNat])
                            (tvar (Id 3)))
                      (tvar (Id 4)).
  Example t7 : prog > cntxt |- app1 ::: TNat.
  Proof.
    apply T_App with (T1 := TNat). apply T_App with (T1 := TNat).
    * apply T_Fun.
      - reflexivity.
      - simpl. apply Forall_cons.
        -- apply D_Nat.
        -- apply Forall_nil.
    * apply T_Var. reflexivity.
    * apply T_Var. reflexivity.
  Qed.

  Example t7a : prog > cntxt |- app1 ::: TNat.
  Proof.
    repeat econstructor.
  Qed.
End Examples.
