{-# OPTIONS --type-in-type --unicode #-}

open import Data.Product
open import Data.Sum.Base
open import Data.Nat
open import Agda.Builtin.Unit
open import Agda.Primitive
open import Category.Monad
open import Function.Base

open import Effect

module Free where

data Free (E : Effect) (A : Set) : Set where
  pure : A → Free E A
  impure : ⟦ E ⟧ (Free E A) → Free E A


Alg : (E : Effect) (A : Set) → Set
Alg E A = ⟦ E ⟧ A → A

fold : {A B : Set} {E : Effect} (g : A → B) → Alg E B → Free E A → B
fold g a (pure x)       = g x
fold g a (impure (op , k))  = a (op , fold g a ∘ k)

_>>=_ : ∀ {A B E} → Free E A → (A → Free E B) → Free E B
m >>= f = fold f impure m

mkFreeMonad : ∀ {E} → RawMonad (Free E)
mkFreeMonad = record
  { return = pure
  ; _>>=_ = _>>=_
  }