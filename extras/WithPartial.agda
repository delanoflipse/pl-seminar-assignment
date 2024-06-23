-- Note: initial attempt at implementing the partiality monad
-- using sized types. This is not the final version

{-# OPTIONS --copatterns --sized-types #-}

open import Size
open import Agda.Primitive
open import Data.Bool
open import Data.Nat

open import Relation.Binary.PropositionalEquality
open import FreeMonads.Structure.FreeMonads.Structure.Effect.Monad

module WithPartial where
  
Type = Set

data Expr : Type where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Loop : Expr

mutual
  data Partial (A : Type) (i : Size) : Type where
    now   : A → Partial A i
    later : ∞Partial A i → Partial A i

  record ∞Partial (A : Type) (i : Size) : Type where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Partial A j


module PartialBind where
  mutual
    _>>=_ : ∀ {i A B} → Partial A i → (A → Partial B i) → Partial B i
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Partial A i → (A → Partial B i) → ∞Partial B i
    force (x ∞>>= f) = force x >>= F

delayMonad : ∀ {i} → RawMonad {f = lzero} (λ A → Partial A i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open PartialBind

module _ {i : Size} where
  open module PartialMonad = RawMonad (delayMonad {i = i}) 
                           public renaming (_⊛_ to _<*>_)

eval : Expr → Partial ℕ
eval (Val n) = Now n
eval (Add e1 e2) = do
  n1 ← eval e1
  n2 ← eval e2
  Now (n1 + n2)
eval Loop = Later (eval Loop)

-- exec : Code → Stack → Partial Stack
