{-# OPTIONS --type-in-type --unicode --guardedness #-}

open import Data.Nat
open import Data.Product
open import Agda.Builtin.Unit

open import Effect
open import Free
-- open import FreeCo

module FreePartial where
-- data Partial (A : Set) : Set where
--   Now : A → Partial A
--   Later : Partial A -> Partial A

data PartialOp : Set where
  LaterOp : PartialOp

open PartialOp

PartialRet : PartialOp → Set
PartialRet LaterOp = ⊤

PartialEffect : Effect
PartialEffect = PartialOp ▷ PartialRet

PartialFree = Free PartialEffect

now : ∀ {A} → A → PartialFree A
now A = pure A

later : ∀ {A} → PartialFree A → PartialFree A
later pa = impure (LaterOp , λ _ → pa)

example : PartialFree ℕ
example = later (now 42)
