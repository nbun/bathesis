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

(* Star tagged variables can only be specialized to non-functional data types,
   while the empty tag allows this *)

Inductive tag : Type :=
 | tag_star  : tag
 | tag_empty : tag.

Inductive ty : Type :=
  | TVar  : id -> ty
  | TBool : ty
  | TNat  : ty
  | TList : ty -> ty
  | TPair : ty -> ty -> ty
  | TFun  : list ty  -> ty -> ty.

Inductive context : Type := 
 | con : (partial_map tag) -> (partial_map ty) -> context.

Definition empty := con emptymap emptymap.
 
Definition typecon (Gamma : context) : (partial_map ty) :=
match Gamma with
 | (con _ tyc) => tyc
end.

Definition tagcon (Gamma : context) : (partial_map tag) :=
match Gamma with
 | (con tagc _) => tagc
end.

Definition type_update (Gamma : context) (x : id) (v : ty) := 
 (con (tagcon Gamma) (update (typecon Gamma) x v)).
 
Definition tag_update (Gamma : context) (x : id) (v : tag) := 
 (con (update (tagcon Gamma) x v) (typecon Gamma)).

Inductive tm : Type :=
  | tvar   : id -> tm
  | tapp   : tm -> tm -> tm
  | tfun   : id -> list ty -> tm
  | tlet   : tm -> tm -> tm -> tm
  | ttrue  : tm
  | tfalse : tm
  | tfail  : ty -> tm
  | tany   : ty -> tm
  | tzero  : tm
  | tsucc  : tm -> tm
  | tadd   : tm -> tm -> tm
  | teqn   : tm -> tm -> tm
  | tpair  : tm -> tm -> tm
  | tnil   : tm
  | tcons  : tm -> tm -> tm
  | tcasep : tm -> tm -> tm
  | tcaseb : tm -> tm -> tm -> tm
  | tcasel : tm -> tm -> tm -> tm.

Inductive quantifier : Type :=
 for_all : id -> tag -> quantifier.

Inductive func_decl : Type :=
 FDecl : id -> list quantifier -> ty -> (list id) -> tm -> func_decl.

Fixpoint qs_to_optys (Gamma : context) (qs : list quantifier) : (list (option ty)) :=
  map (fun q => match q with (for_all id _) => (typecon Gamma id) end) qs.

Fixpoint optys_to_tys (optys : list (option ty)) : (list ty) :=
  match optys with
  | []                 => []
  | (Some ty) :: optys => ty :: (optys_to_tys optys)
  |  None     :: optys =>       (optys_to_tys optys)
  end.

Definition is_star_tagged (q : quantifier) : bool :=
  match q with
  | (for_all _ tag_star)  => true
  | (for_all _ tag_empty) => false
  end.

Definition fd_to_tys (Gamma : context) (fd : func_decl) : (list ty) :=
  match fd with
  | FDecl _ [] _ _ _ => []
  | FDecl _ qs _ _ _ => optys_to_tys (qs_to_optys Gamma (filter is_star_tagged qs))
  end.

Definition beq_fd (fd1 fd2 : func_decl) : bool :=
  match fd1, fd2 with
    | (FDecl m _ _ _ _), (FDecl n _ _ _ _) => if (beq_id m n ) then true else false
  end.
 
Definition program := list func_decl.

Definition lookup_func (p : program) (i : id) :=
 find (fun fd => match fd with (FDecl j _ _ _ _) => (beq_id i j) end) p.

Reserved Notation "Gamma '|-' T '\in_data'" (at level 40).
Inductive data : context -> ty -> Prop :=
  | D_Var :  forall Gamma n,
              (tagcon Gamma) n  = Some tag_star ->
              Gamma |- (TVar n) \in_data
  | D_Bool : forall Gamma, Gamma |- TBool \in_data
  | D_Nat :  forall Gamma, Gamma |- TNat \in_data
  | D_List : forall Gamma T,
               Gamma |- T \in_data ->
               Gamma |- (TList T) \in_data
  | D_Pair : forall Gamma T T', 
               Gamma |- T \in_data ->
               Gamma |- T' \in_data ->
               Gamma |- (TPair T T') \in_data
where "Gamma '|-' T '\in_data'" := (data Gamma T).

Fixpoint ty_subst (k: id) (t: ty) (t': ty) : ty :=
  match t' with
   | TVar i      =>  if (beq_id i k) then t else TVar i
   | TBool       => TBool
   | TNat        => TNat
   | TList T     => TList (ty_subst k t T)
   | TPair TL TR => TPair (ty_subst k t TL) (ty_subst k t TR)
   | TFun tys ty => TFun (map (ty_subst k t) tys) (ty_subst k t ty)
  end.

Fixpoint qty_zip (qs : list quantifier) (tys : list ty) : (list (quantifier * ty)) :=
  match qs, tys with
   | [],        []          => []
   | [],        (ty :: _)   => [] (* todo: error handling *)
   | (q :: _),  []          => [] (* todo: error handling *)
   | (q :: qs), (ty :: tys) => (q, ty) :: (qty_zip qs tys)
  end.

Definition multi_ty_subst (qtys : list (quantifier * ty)) (t : ty) : ty := 
 fold_right (fun qty t => match qty with (for_all id _, ty) => ty_subst id ty t end) t qtys.
  
Definition specialize_func (fd : func_decl) (tys : list ty) : option ty := 
  match fd with
   | (FDecl _ qs t _ _) => if (beq_nat (length qs) (length tys))
                           then Some (multi_ty_subst (qty_zip qs tys) t)
                           else None
  end.
  
Definition func_rty (t : ty) : ty :=
  match t with
  | TFun _ rty => rty
  | _          => t
  end.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var :    forall Gamma x T,
                 (typecon Gamma) x = Some T ->
                 Gamma |- tvar x \in T
  | T_True :   forall Gamma, 
                 Gamma |- ttrue \in TBool
  | T_False :  forall Gamma,
                 Gamma |- tfalse \in TBool
  | T_Zero :   forall Gamma,
                 Gamma |- tzero \in TNat
  | T_Succ :   forall Gamma e,
                 Gamma |- e \in TNat -> 
                 Gamma |- (tsucc e) \in TNat
  | T_Nil :    forall Gamma T, 
                 Gamma |- tnil \in (TList T)
  | T_App :    forall Gamma e1 e2 T1 T2,
                 Gamma |- e1 \in (TFun [T1] T2) ->
                 Gamma |- e2 \in T1 ->
                 Gamma |- (tapp e1 e2) \in T2
  | T_Let :    forall Gamma e1 e2 x T1 T2,
                 Gamma |- e1 \in T1 ->
                 (type_update Gamma x T1) |- e2 \in T2 ->
                 Gamma |- (tlet (tvar x) e1 e2) \in T2
  | T_Fun :    forall Gamma P id fd tys t rty,
                 lookup_func P id = Some fd ->
                 specialize_func fd tys = Some t ->
                 (func_rty t) = rty ->
                 Forall (data Gamma) (fd_to_tys Gamma fd) ->
                 Gamma |- (tfun id tys) \in rty
  | T_Add :    forall Gamma e1 e2,
                 Gamma |- e1 \in TNat ->
                 Gamma |- e2 \in TNat ->
                 Gamma |- (tadd e1 e2) \in TNat
  | T_EqN :    forall Gamma e1 e2,
                 Gamma |- e1 \in TNat ->
                 Gamma |- e2 \in TNat ->
                 Gamma |- (teqn e1 e2) \in TBool
  | T_Pair:    forall Gamma e1 e2 T1 T2,
                 Gamma |- e1 \in T1 ->
                 Gamma |- e2 \in T2 ->
                 Gamma |- (tpair e1 e2) \in (TPair T1 T2)
  | T_Cons :   forall Gamma e1 e2 T,
                 Gamma |- e1 \in T ->
                 Gamma |- e2 \in (TList T) -> 
                 Gamma |- (tcons e1 e2) \in (TList T)
  | T_CaseL :  forall Gamma e e1 e2 h t T T',
                 Gamma |- e \in (TList T') ->
                 Gamma |- e1 \in T ->
                 (type_update (type_update Gamma h T') t (TList T')) |- e2 \in T ->
                 Gamma |- (tcasel e e1 e2) \in T
  | T_CaseP :  forall Gamma e e1 l r T T1 T2,
                 Gamma |- e \in (TPair T1 T2) ->
                 (type_update (type_update Gamma l T1) r T2) |- e1 \in T ->
                 Gamma |- (tcasep e e1) \in T
  | T_CaseB :  forall Gamma e e1 e2 T,
                 Gamma |- e \in TBool ->
                 Gamma |- e1 \in T ->
                 Gamma |- e2 \in T ->
                 Gamma |- (tcaseb e e1 e2) \in T
  | T_Fail :   forall Gamma T,
                 Gamma |- (tfail T) \in T
  | T_Any :    forall Gamma T,
                 Gamma |- T \in_data ->
                 Gamma |- (tany T) \in T
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
  
Section Examples.
  Example t1 : empty |- ttrue \in TBool.
  Proof. apply T_True. Qed.
  
  Definition c := (type_update empty (Id 5) TNat).
  
  Example t2 : c |- (tvar (Id 5)) \in TNat.
  Proof. apply T_Var. reflexivity. Qed.
  
  Example t3 : empty |- (tlet (tvar (Id 5)) tzero (tadd (tsucc tzero) (tvar (Id 5)))) \in TNat.
  Proof. apply T_Let with (T1 := TNat).
         apply T_Zero.
         apply T_Add.
         apply T_Succ. apply T_Zero.
         apply T_Var. reflexivity.
  Qed.
  
  Example t4 : empty |- (tcasel tnil tnil (tcons (tsucc tzero) tnil)) \in (TList TNat).
  Proof. apply T_CaseL with (T' := TNat) (h := Id 5) (t := Id 6).
         apply T_Nil.
         apply T_Nil.
         apply T_Cons.
         apply T_Succ. apply T_Zero.
         apply T_Nil.
  Qed.
  
  Example t5 : (type_update empty (Id 5) TBool) |- (tcasel (tcons ttrue tnil) tfalse (tvar (Id 5))) \in TBool.
  Proof. apply T_CaseL with (T' := TBool) (h := Id 6) (t := Id 7).
         apply T_Cons.
         apply T_True.
         apply T_Nil.
         apply T_False.
         apply T_Var. reflexivity.
  Qed.

  Definition aContext :=
    type_update (type_update (type_update empty (Id 5) TNat) (Id 51) TBool) (Id 2) (TVar (Id 1)).

  Example t6 : aContext |- tvar (Id 2) \in TVar (Id 1).
  Proof. apply T_Var. reflexivity. Qed.
  
  Example multi_t1 : multi_ty_subst [((for_all (Id 1) tag_empty), TNat);((for_all (Id 2) tag_empty), (TList TBool))] (TFun [TVar (Id 1); (TVar (Id 2))] TNat) = (TFun [TNat; TList TBool] TNat).
  Proof. reflexivity. Qed.
  
  Example ty_subst1 : ty_subst (Id 1) TBool (TFun [(TVar (Id 1))] (TVar (Id 1))) = TFun [TBool] TBool.
  Proof. reflexivity. Qed.
  
  Definition prog := [FDecl (Id 1) [(for_all (Id 5) tag_star)] (TFun [TVar (Id 5)] (TVar (Id 5))) [Id 1] (tvar (Id 1))].
  Definition prog_fd := FDecl (Id 1) [(for_all (Id 5) tag_star)] (TFun [TVar (Id 5)] (TVar (Id 5))) [Id 1] (tvar (Id 1)).

  Example fun1 : aContext |- (tfun (Id 1) [TNat]) \in TNat.
  Proof. apply T_Fun with (P := prog) (fd := prog_fd) (t := TFun [TNat] TNat).
  reflexivity.
  reflexivity.
  reflexivity.
  simpl. apply Forall_cons. apply D_Nat. apply Forall_nil.
  Qed.

End Examples.