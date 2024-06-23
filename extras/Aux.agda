-- Note: This file is here to play around with monad definition in Agda.
-- Not used in the final implementation.

open import Agda.Builtin.Equality

-- https://www.cs.bham.ac.uk/~mhe/fp-learning-2017-2018/html/monads.html
module Aux where

Type = Set
LargeType = Set₁

record Monad (M : Type → Type) : LargeType where
  constructor
    makeMonad

  field
    return : {X : Type} → X → M X

    _>>=_  : {X Y : Type} → M X → (X → M Y) → M Y

    requirement₀ : {X Y : Type} (x : X) (f : X → M Y)
                → (return x >>= f) ≡ f x

    requirement₁ : {X : Type} (m : M X)
                → (m >>= return) ≡ m

    requirement₂ : {X Y Z : Type} (m : M _) (f : X → M Y) (g : Y → M Z)
                → ((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g))

record RawMonad (M : Type → Type) : LargeType where
  constructor
    makeRawMonad

  field
    return : {X : Type} → X → M X

    _>>=_  : {X Y : Type} → M X → (X → M Y) → M Y
