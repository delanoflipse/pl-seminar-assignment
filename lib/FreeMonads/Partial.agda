{-# OPTIONS --type-in-type --unicode --guardedness #-}

open import Data.Nat
open import Data.Product
open import Agda.Builtin.Unit

open import FreeMonads.Structure.Effect
open import FreeMonads.Structure.Free
open import FreeMonads.Structure.Coinductive

module FreeMonads.Partial where

-- Original definition of Partial:
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
PartialCofree = Cofree PartialEffect

now : ∀ {A} → A → PartialFree A
now A = pure A

∞now : ∀ {A} → A → PartialCofree A
∞now A = inp (pure A)

later : ∀ {A} → PartialFree A → PartialFree A
later pa = impure (LaterOp , λ _ → pa)

∞later : ∀ {A} → PartialFree A → PartialCofree A
∞later pa = inp (impure (LaterOp , λ _ → pa))

example : PartialFree ℕ
example = later (now 42)
