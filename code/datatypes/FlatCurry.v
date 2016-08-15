Require Import Reals String Datatypes Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Inductive Literal : Type :=
  | Intc   : nat    -> Literal
  | Floatc : R      -> Literal
  | Charc  : string -> Literal.
 
Inductive Visibility : Type :=
  | Public  : Visibility
  | Private : Visibility.
 
Definition TVarIndex := nat.
Definition VarIndex  := nat.

Definition QName := (prod string string).

Inductive TypeExpr : Type :=
  | TVar     : TVarIndex -> TypeExpr
  | FuncType : TypeExpr  -> TypeExpr      -> TypeExpr
  | TCons    : QName     -> list TypeExpr -> TypeExpr.

Definition Int   := TCons ("Prelude", "Int"  ) [].
Definition Float := TCons ("Prelude", "Float") [].
Definition Char  := TCons ("Prelude", "Char" ) [].

Inductive ConsDecl : Type :=
  | Cons :  QName -> nat -> Visibility -> list TypeExpr -> ConsDecl.

(* Type is a keyword! *)
Inductive TypeDecl : Type :=
  | Typec   : QName -> Visibility -> list TVarIndex -> list ConsDecl -> TypeDecl
  | TypeSyn : QName -> Visibility -> list TVarIndex -> TypeExpr      -> TypeDecl.

Inductive Fixity : Type :=
  | InfixOp  : Fixity 
  | InfixlOp : Fixity
  | InfixrOp : Fixity.

Inductive OpDecl : Type :=
  | Op : QName -> Fixity -> nat -> OpDecl.

Inductive CaseType : Type :=
  | Rigid : CaseType
  | Flex  : CaseType.

Inductive CombType : Type := 
  | FuncCall     : CombType
  | ConsCall     : CombType
  | FuncPartCall : nat -> CombType 
  | ConsPartCall : nat -> CombType.

(* Type and constructor can't use identical names! *)
Inductive TPattern : Type := 
  | Pattern : QName -> list VarIndex -> TPattern
  | LPattern : Literal -> TPattern.

Inductive Expr : Type := 
  | Var   : VarIndex -> Expr
  | Lit   : Literal -> Expr
  | Comb  : CombType -> QName -> list Expr -> Expr
  | Let   : list (prod VarIndex Expr) -> Expr -> Expr
  | Free  : list VarIndex -> Expr -> Expr
  | Or    : Expr -> Expr -> Expr
  | Case  : CaseType -> Expr -> list BranchExpr -> Expr
  | Typed : Expr -> TypeExpr -> Expr
with
BranchExpr :=
  | Branch : TPattern -> Expr -> BranchExpr.

(* Type and constructor can't use identical names! *)
Inductive TRule : Type := 
  | Rule : list VarIndex -> Expr -> TRule
  | External : string -> TRule.

Inductive FuncDecl : Type := 
  | Func : QName -> nat -> Visibility -> TypeExpr -> TRule -> FuncDecl.

(* Type and constructor can't use identical names! *)
Inductive TProg : Type := 
  | Prog : string -> list string -> list TypeDecl -> list FuncDecl -> list OpDecl -> TProg.
