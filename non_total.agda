open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Expr : Set where
  Val : Nat → Expr
  Add : Expr → Expr → Expr
  Loop : Expr
  
eval : Expr → Nat
eval (Val n) = n
eval (Add x y) = eval x + eval y
-- Termination check fails
eval Loop = eval Loop
