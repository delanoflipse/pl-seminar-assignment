{-# OPTIONS --type-in-type --unicode --guardedness #-}

open import Data.Nat
open import Data.Product
open import Data.Sum.Base

open import FreeMonads.Structure.Free
open import FreeMonads.Structure.Effect
open import FreeMonads.Partial
open import FreeMonads.NonDeterminism

module FreeMonads.PartialNonDeterminism where

PNDEffect = PartialEffect :+: NDEffect
FreePND = Free PNDEffect

examplepnd : FreePND ℕ
examplepnd = impure ((inj₁ LaterOp), λ x → 
  impure (inj₂ ZeroOp , λ ()))
-- inj₁ (LaterOp , λ x → ?