{-# OPTIONS --type-in-type --unicode --overlapping-instances #-}

open import Function.Base
open import Data.Product
open import Data.Sum.Base

module FreeMonads.Structure.Effect where

infix 5 _▷_

-- record Container : Set where
--   constructor _▷_
--   field
--     Shape    : Set
--     Position : Shape → Set
-- open Container public

-- ⟦_⟧ :  Container → Set → Set
-- ⟦ S ▷ P ⟧ X = Σ[ s ∈ S ] (P s → X)

record Effect : Set where
  constructor _▷_
  field
    Op  : Set       -- Set of operations
    Ret : Op → Set  -- Return type for each operation in the set

⟦_⟧ :  Effect → Set → _
⟦ Op ▷ Ret ⟧ X = Σ[ op ∈ Op ] (Ret op → X)

infix 12 _:+:_
_:+:_ : Effect → Effect → Effect
(Op1 ▷ Ret1) :+: (Op2 ▷ Ret2) = Op3 ▷ Ret3 where
  Op3 = Op1 ⊎ Op2
  Ret3 = [ Ret1 , Ret2 ]

map-sig : {X Y : Set} {E : Effect} (f : X → Y ) → ⟦ E ⟧ X → ⟦ E ⟧ Y
map-sig f (op , k) = (op , f ∘ k)


-- Row insertions --


variable Δ Δ′ Δ″ Δ‴ Δ₀ Δ₁ Δ₂ Δ₃ : Effect

data _∼_▸_ : Effect → Effect → Effect → Set₁ where
  insert :                 (Δ₀ :+: Δ′) ∼ Δ₀ ▸ Δ′
  sift   : (Δ ∼ Δ₀ ▸ Δ′) → ((Δ₁ :+: Δ) ∼ Δ₀ ▸ (Δ₁ :+: Δ′))

_≲_ : Effect → Effect → Set
E1 ≲ E2 = ∃ λ (E : Effect) → E1 ∼ E ▸ E2 

instance
  insert▸ : (Δ₀ :+: Δ′) ∼ Δ₀ ▸ Δ′
  insert▸ = insert

  sift▸ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → ((Δ₁ :+: Δ) ∼ Δ₀ ▸ (Δ₁ :+: Δ′))
  sift▸ ⦃ w ⦄ = sift w

