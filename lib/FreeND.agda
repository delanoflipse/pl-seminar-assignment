{-# OPTIONS --type-in-type --unicode #-}

open import Data.Product
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Bool

open import Effect
open import Free

-- data ND (A : Set): Set where
--   ret   : A → ND A
--   zero  : ND A
--   _⊕_   : ND A → ND A → ND A

module FreeND where

data ND_Op : Set where
  ZeroOp    : ND_Op
  ChoiceOp  : ND_Op

ND_Ret : ND_Op → Set
ND_Ret ZeroOp = ⊥
ND_Ret ChoiceOp = Bool

ND_Effect : Effect
ND_Effect = ND_Op ▷ ND_Ret

ND_Free = Free ND_Effect

ret : ∀ {A} → A → ND_Free A
ret A = pure A

zero : ∀ {A} → ND_Free A
zero = impure (ZeroOp , λ ())

infixl 8 _⊕_

_⊕_ : ∀ {A} → ND_Free A → ND_Free A → ND_Free A
op₁ ⊕ op₂ = impure (ChoiceOp , λ b → if b then op₁ else op₂)

-- ND_Ret : ND_Op → Set
-- ND_Ret zero = ⊥
-- ND_Ret (choice op₁ op₂) = ND_Ret op₁ × ND_Ret op₂

-- zeroF : ∀ {A} → ND_Free A
-- zeroF = impure (inj zero , ⊥-elim)

-- _[+]_ : ∀ {A} → ND_Free A → ND_Free A → ND_Free A
-- op₁ [+] op₂ = impure (choice op₁ op₂ , _)

