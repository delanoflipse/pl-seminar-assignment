{-# OPTIONS --cubical #-}

open import Data.Container
open import Agda.Primitive
open import Level as L
open import Category.Functor

module FreeMonad where

-- data Free {l'} (F : ∀ l → Set l → Set l') (A : Set) : Set where
--   pure    : A → Free F A
--   impure  : (F (Free F A)) → Free F A

Container00 : Set₁
Container00 = Container L.zero L.zero

data Free (F : Container00) (A : Set) : Set where
    pure : A → Free F A
    free : ⟦ F ⟧ (Free F A) → Free F A

-- mutual
--   data Free {l l'} (F : Set l → Set l') (A : Set) (i : Size) : Set (l ⊔ l') where
--     pure    : A → Free F A i
--     later : F (∞Free F A i) → Free F A i

--   record ∞Free {l l'} (F : Set l → Set l') (A : Set) (i : Size) : Set (l ⊔ l') where
--     coinductive
--     constructor delay
--     field
--       force : {j : Size< i} → Free F A j
  