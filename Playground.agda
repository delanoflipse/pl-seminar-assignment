{-# OPTIONS --guardedness  #-}
open import Agda.Builtin.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

apply : (A : Set)(B : A -> Set) -> ((x : A) -> B x) -> (a : A) -> B a
apply A B f a = f a


record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A


-- from : Nat → Stream Nat
-- from n = record { head = n; tail = from (suc n) }

-- subst : {P : Set → Set} → {x y : Set} → x ≡ y → P y → P x
-- subst refl p = p

_+'_ : Nat → Nat → Nat
zero +' m = m
(suc n) +' m = suc (n + m)

x = 3 +' 4

_ : x ≡ 7
_ = begin
  x
  ≡⟨⟩
  3 +' 4
  ≡⟨⟩
  7
  ∎

-- or
_ : x ≡ 7
_ = refl

+-assoc : ∀ (m n p : Nat) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ {!   !} ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎
