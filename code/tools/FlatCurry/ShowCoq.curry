------------------------------------------------------------------------------
--- This library contains operations to transform FlatCurry programs
--- into string representations in Coq syntax.
---
--- This library contains the following show functions for a conversion of 
--- FlatCurry programs: (`showFlatProgCoq`, `showFlatTypeCoq`, `showFlatFuncCoq`)
---
--- @author Michael Hanus, adapted by Niels Bunkenburg
--- @version August 2016, 
--- @category meta
------------------------------------------------------------------------------

module FlatCurry.ShowCoq(showFlatProgCoq,showFlatTypeCoq,showFlatFuncCoq)
   where

import FlatCurry.Types
import List
import Char

--- Shows a FlatCurry program term as a string (with some pretty printing).
showFlatProgCoq :: Prog -> String
showFlatProgCoq (Prog modname imports types funcs ops) =
     " (Prog " ++ show modname
     ++ (if imports==[] then "\n  []" else
         "\n  [" ++ showFlatListElems show imports ++ "]")
     ++ (if types==[] then "\n  []" else
         "\n  [" ++ showFlatListElems showFlatTypeCoq types ++ "\n ]")
     ++ "\n  [" ++ showFlatListElems showFlatFuncCoq funcs ++ "\n  ]"
     ++ "\n " ++ showFlatList showFlatOp ops
     ++ "\n )\n"

showFlatVisibility Public  = " Public "
showFlatVisibility Private = " Private "

showFlatFixity InfixOp = " InfixOp "
showFlatFixity InfixlOp = " InfixlOp "
showFlatFixity InfixrOp = " InfixrOp "

showFlatOp (Op name fix prec) =
 "(Op " ++ show name ++ showFlatFixity fix ++ show prec ++ ")"

 -- Coq: "Type" is a reserved keyword, use "Typec" instead
showFlatTypeCoq :: TypeDecl -> String
showFlatTypeCoq (Type name vis tpars consdecls) =
  "\n  (Typec " ++ show name ++ showFlatVisibility vis
               ++ showFlatList show tpars
               ++ showFlatList showFlatCons consdecls ++ ")"
showFlatTypeCoq (TypeSyn name vis tpars texp) =
  "\n  (TypeSyn " ++ show name ++ showFlatVisibility vis
                  ++ showFlatList show tpars
                  ++ showFlatTypeExpr texp ++ ")"

showFlatCons (Cons cname arity vis types) =
  "(Cons " ++ show cname ++ " " ++ show arity
           ++ showFlatVisibility vis
           ++ showFlatList showFlatTypeExpr types ++ ")"

showFlatFuncCoq :: FuncDecl -> String
showFlatFuncCoq (Func name arity vis ftype rl) =
  "\n  (Func " ++ show name ++ " " ++ show arity ++ " "
               ++ showFlatVisibility vis ++
  "\n        " ++ showFlatTypeExpr ftype ++
  "\n       " ++ showFlatRule rl ++ ")"

showFlatRule (Rule params expr) =
  " (Rule " ++ showFlatList show params
            ++ showFlatExpr expr ++ ")"
showFlatRule (External name) =
  " (External " ++ show name ++ ")"

showFlatTypeExpr (FuncType t1 t2) =
  "(FuncType " ++ showFlatTypeExpr t1 ++ " " ++ showFlatTypeExpr t2 ++ ")"
showFlatTypeExpr (TCons tc ts) =
  "(TCons " ++ show tc
            ++ showFlatList showFlatTypeExpr ts ++ ")"
showFlatTypeExpr (TVar n) = "(TVar " ++ show n ++ ")"


showFlatCombType FuncCall = "FuncCall"
showFlatCombType ConsCall = "ConsCall"
showFlatCombType (FuncPartCall n) = "(FuncPartCall " ++ show n ++ ")"
showFlatCombType (ConsPartCall n) = "(ConsPartCall " ++ show n ++ ")"

showFlatExpr (Var n) = "(Var " ++ show n ++ ")"
showFlatExpr (Lit l) = "(Lit " ++ showFlatLit l ++ ")"
showFlatExpr (Comb ctype cf es) =
  "(Comb " ++ showFlatCombType ctype ++ " "
           ++ show cf ++ showFlatList showFlatExpr es ++ ")"
showFlatExpr (Let bindings exp) =
  "(Let " ++ showFlatList showFlatBinding bindings ++ showFlatExpr exp ++ ")"
 where showFlatBinding (x,e) = "("++show x++","++showFlatExpr e++")"
showFlatExpr (Free xs e) =
  "(Free " ++ showFlatList show xs ++ showFlatExpr e ++ ")"
showFlatExpr (Or e1 e2) =
  "(Or " ++ showFlatExpr e1 ++ " " ++ showFlatExpr e2 ++ ")"
showFlatExpr (Case Rigid e bs) =
  "(Case Rigid " ++ showFlatExpr e ++ showFlatList showFlatBranch bs ++ ")"
showFlatExpr (Case Flex e bs) =
  "(Case Flex " ++ showFlatExpr e ++ showFlatList showFlatBranch bs ++ ")"
showFlatExpr (Typed e ty) =
  "(Typed " ++ showFlatExpr e ++ ' ' : showFlatTypeExpr ty ++ ")"

showFlatLit (Intc   i) = "(Intc " ++ show i ++ ")"
showFlatLit (Floatc f) = "(Floatc " ++ show f ++ ")"
-- Coq: Characters are enclosed by double quotes instead of single quotes
showFlatLit (Charc  c) = "(Charc \"" ++ escQuote (filter (/='\'') (show c)) ++ "\")"

-- Coq: Escape double quotes by adding another double quote
escQuote :: String -> String
escQuote [] = []
escQuote (c:s) = case c of
                      '"' -> ['"','"']
                      otherwise -> [c] ++ escQuote s

showFlatBranch (Branch p e) = "(Branch " ++ showFlatPattern p
                                         ++ showFlatExpr e ++ ")"

showFlatPattern (Pattern qn xs) =
      "(Pattern " ++ show qn
                  ++ showFlatList show xs ++ ")"
showFlatPattern (LPattern lit) = "(LPattern " ++ showFlatLit lit ++ ")"


-- format a finite list of elements:
showFlatList :: (a->String) -> [a] -> String
showFlatList format elems = " [" ++ showFlatListElems format elems ++ "] "

-- Coq: List elements are separated by semicolons 
showFlatListElems :: (a->String) -> [a] -> String
showFlatListElems format elems = concat (intersperse ";" (map format elems))
