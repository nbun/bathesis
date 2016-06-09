Inductive tm : Type :=
  | tvar : tm
  | tapp : tm -> tm -> tm
  | tfun : tm -> tm -> tm
  | tlet : tm -> tm -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tfailure : tm
  | tanyting : tm
  | tzero : tm
  | tsucc : tm -> tm
  | tadd : tm -> tm -> tm
  | teqn : tm -> tm -> tm
  | tpair : tm -> tm -> tm
  | tnil : tm
  | tcons : tm -> tm -> tm
  | tcasep : tm -> tm -> tm (* ? *)
  | tcaseb : tm -> tm -> tm -> tm
  | tcasel : tm -> tm -> tm -> tm.
  
Inductive ty : Type :=
  | TVar : ty
  | TBool : ty
  | TNat : ty
  | TList : ty -> ty
  | TPair : ty -> ty -> ty
  | TFun : ty -> ty -> ty.
  
Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Var :    |- tvar \in TVar (* ? *)
  | T_True :   |- ttrue \in TBool
  | T_False :  |- tfalse \in TBool
  | T_Zero :   |- tzero \in TNat
  | T_Succ :   forall e,
               |- e \in TNat -> 
               |- (tsucc e) \in TNat
  | T_Nil :    forall T, |- tnil \in (TList T)
  | T_App :    forall e1 e2 T1 T2,
               |- e1 \in (TFun T1 T2) ->
               |- e2 \in T1 ->
               |- (tapp e1 e2) \in T2
  | T_Let :    forall e1 e2 x T1 T2,
               |- e1 \in T1 ->
               |- x \in T1 ->
               |- e2 \in T2 ->
               |- (tlet x e1 e2) \in T2
(*| T_Fun*)
  | T_Add :    forall e1 e2,
               |- e1 \in TNat ->
               |- e2 \in TNat ->
               |- (tadd e1 e2) \in TNat
  | T_EqN :    forall e1 e2,
               |- e1 \in TNat ->
               |- e2 \in TNat ->
               |- (teqn e1 e2) \in TBool
  | T_Pair:    forall e1 e2 T1 T2,
               |- e1 \in T1 ->
               |- e2 \in T2 ->
               |- (tpair e1 e2) \in (TPair T1 T2)
  | T_Cons :   forall e1 e2 T,
               |- e1 \in T ->
               |- e2 \in (TList T) -> 
               |- (tcons e1 e2) \in (TList T)
(*| T_CaseL :  forall e e1 e2 h t T T',
               |- e \in (TList T') ->
               |- e1 \in T ->
               |- h \in T' ->
               |- t \in (TList T') ->
               |- e2 \in T1 ->
               |- (tcasel e e1 e2) \in T
  | T_CaseP :  forall e e1 T T1 T2
               |- e \in (TPair T1 T2) ->
               |- l \in T1 ->
               |- r \in T2 ->
               |- e1 \in T ->
               |- (tcasep e e1) \in T *)
  | T_CaseB :  forall e e1 e2 T,
               |- e \in TBool ->
               |- e1 \in T ->
               |- e2 \in T ->
               |- (tcaseb e e1 e2) \in T
  | T_Fail :   forall T, |- tfailure \in T
  
where "'|-' t '\in' T" := (has_type t T).

(* anything -> Data type rules? *)