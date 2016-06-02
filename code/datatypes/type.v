Require Import flatCurry.

Inductive tm : Type := 
  | TBase : BaseType -> tm
  | TFunc : tm       -> tm -> tm
  | TCons : QName    -> tm
  with 
  BaseType :=
  | Var   : nat -> BaseType
  | Int   : BaseType
  | Float : BaseType
  | Bool  : BaseType
  | Char  : BaseType
  | IO    : BaseType.
  
Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | TFuncStep     : forall t1 t2, (TFunc t1 t2) ==> t2
  | TFuncStepTrans: forall t1 t2 t3, t1 ==> t2 -> t2 ==> t3 -> t1 ==> t3
  | TFuncStepPartL: forall t1 t2 t3, (TFunc t1 (TFunc t2 t3)) ==> (TFunc t1 t3)
  | TFuncStepPartR: forall t1 t2 t3, (TFunc (TFunc t1 t2) t3) ==> (TFunc t2 t3)
  | TFuncStepEvalL    : forall t1 t1' t2,
                      t1 ==> t1' -> (TFunc t1 t2) ==> (TFunc t1' t2)
  | TFuncStepEvalR    : forall t1 t2 t2',
                      t2 ==> t2' -> (TFunc t1 t2) ==> (TFunc t1 t2')
  where "t1 '==>' t2" := (step t1 t2).

Example e1 : (TFunc (TBase Int) (TFunc (TBase Char) (TBase Int))) ==> (TBase Int).
Proof.
  assert (TFunc (TBase Int) (TFunc (TBase Char) (TBase Int)) ==> (TFunc (TBase Int) (TBase Int))).
  apply TFuncStepPartL.
  assert (TFunc (TBase Int) (TBase Int) ==> (TBase Int)).
  apply TFuncStep.
  apply TFuncStepTrans with (t2:=TFunc (TBase Int) (TBase Int)).
  apply H. apply H0.
Qed.

Example e2 : (TFunc (TBase (Var 0)) (TFunc (TBase (Var 1)) (TBase (Var 0)))) ==> (TBase (Var 0)).
Proof.
  assert (TFunc (TBase (Var 0)) (TFunc (TBase (Var 1)) (TBase (Var 0))) ==> (TFunc (TBase (Var 0)) (TBase (Var 0)))).
  apply TFuncStepPartL.
  assert (TFunc (TBase (Var 0)) (TBase (Var 0)) ==> (TBase (Var 0))).
  apply TFuncStep.
  apply TFuncStepTrans with (t2:=TFunc (TBase (Var 0)) (TBase (Var 0))).
  apply H. apply H0.
Qed.
