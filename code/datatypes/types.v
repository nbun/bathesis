Require Import NArith ZArith Reals String.
Require Import Coq.Init.Datatypes.
Open Scope N_scope.
Open Scope string_scope.
Open Scope list_scope.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.
  
Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Inductive Literal : Type :=
  | Intc   : Z      -> Literal
  | Floatc : R      -> Literal
  | Charc  : string -> Literal.
 
Inductive Visibility : Type :=
  | Public  : Visibility
  | Private : Visibility.
 
Definition TVarIndex := N.
Definition VarIndex  := N.

Definition QName := (prod string string).

Inductive TypeExpr : Type :=
  | TVar     : TVarIndex            -> TypeExpr
  | FuncType : TypeExpr -> TypeExpr -> TypeExpr
  | TCons    : QName -> list TypeExpr -> TypeExpr.

Inductive ConsDecl : Type :=
  | Cons :  QName -> N -> Visibility -> list TypeExpr -> ConsDecl.

(* Type is a keyword! *)
Inductive TypeDecl : Type :=
  | Typec   : QName -> Visibility -> list TVarIndex -> list ConsDecl -> TypeDecl
  | TypeSyn : QName -> Visibility -> list TVarIndex -> TypeExpr      -> TypeDecl.

Inductive Fixity : Type :=
  | InfixOp  : Fixity 
  | InfixlOp : Fixity
  | InfixrOp : Fixity.

Inductive OpDecl : Type :=
  | Op : QName -> Fixity -> N -> OpDecl.

Inductive CaseType : Type :=
  | Rigid : CaseType
  | Flex  : CaseType.

Inductive CombType : Type := 
  | FuncCall     : CombType
  | ConsCall     : CombType
  | FuncPartCall : N -> CombType 
  | ConsPartCall : N -> CombType.

(* Type and constructor can't use identival names! *)
Inductive Pattern : Type := 
  | Patternc : QName -> list VarIndex -> Pattern
  | LPattern : Literal -> Pattern.

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
  | Branch : Pattern -> Expr -> BranchExpr.

(* Type and constructor can't use identical names! *)
Inductive Rule : Type := 
  | Rulec : list VarIndex -> Expr -> Rule
  | External : string -> Rule.

Inductive FuncDecl : Type := 
  | Func : QName -> N -> Visibility -> TypeExpr -> Rule -> FuncDecl.

(* Type and constructor can't use identical names! *)
Inductive Prog : Type := 
  | Progc : string -> list string -> list TypeDecl -> list FuncDecl -> list OpDecl -> Prog.

Check  (Progc "test"
  (cons "Prelude" nil)
  nil
  (cons
  (Func ("test","function") 0  Public 
        (TCons ("Prelude","Int") nil )
        (Rulec  nil (Lit (Intc 5))))
  nil)
  nil
 ).
