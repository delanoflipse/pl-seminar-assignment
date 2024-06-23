-- Note: this file contains some exercises from the book https://plfa.github.io/
-- To help me get started in Agda

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
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

cong-app' : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x) → f x ≡ g x
cong-app' refl x = refl

subst' : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y

subst' P refl Px = Px

trans' : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z

trans' {x = x} {y = y} {z = z} x=y y=z =
  begin
    x
  ≡⟨ x=y ⟩
    y
  ≡⟨ y=z ⟩
    z
  ∎

+-identity : ∀ (n : Nat) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) = cong suc (+-identity n)

+-suc : ∀  (m n : Nat) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ {n m : Nat} → n + m ≡ m + n
+-comm {n = n} {m = zero} = (+-identity n)
+-comm {n = n} {m = suc m} = trans (+-suc n m) (cong suc (+-comm {n = n} {m = m}))