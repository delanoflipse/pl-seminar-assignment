{-# OPTIONS --type-in-type --unicode #-}

open import Data.Product
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
open import Axiom.Extensionality.Propositional

open import FreeMonads.Structure.Effect
open import FreeMonads.Structure.Free

-- Original definition of ND:
-- data ND (A : Set): Set where
--   ret   : A → ND A
--   zero  : ND A
--   _⊕_   : ND A → ND A → ND A

module FreeMonads.NonDeterminism where

data NDOp : Set where
  ZeroOp    : NDOp
  ChoiceOp  : NDOp

NDRet : NDOp → Set
NDRet ZeroOp = ⊥
NDRet ChoiceOp = Bool

NDEffect : Effect
-- NDEffect = NDOp ▷ NDRet
NDEffect = record { Op = NDOp ; Ret = NDRet }

NDFree = Free NDEffect

ret : ∀ {A} → A → NDFree A
ret A = pure A

zero : ∀ {A} → NDFree A
zero = impure (ZeroOp , λ ())

infixl 8 _⊕_

_⊕_ : ∀ {A} → NDFree A → NDFree A → NDFree A
op₁ ⊕ op₂ = impure (ChoiceOp , λ b → if b then op₁ else op₂)

⊕-inj : ∀ {A} {p q p′ q′ : Free NDEffect A}
      → p ⊕ q ≡ p′ ⊕ q′ → (p ≡ p′) × (q ≡ q′)
⊕-inj x with f-inj (impure-inj x)
... | q = (q true) , (q false)
