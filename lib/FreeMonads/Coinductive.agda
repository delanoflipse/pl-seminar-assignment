{-# OPTIONS --type-in-type --unicode --guardedness #-}

open import Data.Product
open import Data.Sum.Base
open import Data.Nat
open import Agda.Builtin.Unit
open import Agda.Primitive
open import Category.Monad

open import FreeMonads.Structure.Effect
open import FreeMonads.Structure.Free

module FreeMonads.Coinductive where

data FreeF (F : Effect → Set → Set) (E : Effect) (A : Set) : Set where
  pure   : A → FreeF F E A
  impure : ⟦ E ⟧ (F E A) → FreeF F E A

record FreeCo (E : Effect) (A : Set) : Set where
  constructor inp
  coinductive
  field
    inp : FreeF Free E A
