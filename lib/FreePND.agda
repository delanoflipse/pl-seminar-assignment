{-# OPTIONS --type-in-type --unicode --guardedness #-}

open import Data.Nat
open import Data.Product
open import Data.Sum.Base

open import FreePartial
open import FreeND
open import Free
open import Effect

module FreePND where

PNDEffect = PartialEffect :+: NDEffect
FreePND = Free PNDEffect

examplepnd : FreePND ℕ
examplepnd = impure ((inj₁ LaterOp), λ x → 
  impure (inj₂ ZeroOp , λ ()))
-- inj₁ (LaterOp , λ x → ?