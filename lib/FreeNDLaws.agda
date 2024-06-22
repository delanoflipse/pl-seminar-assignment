open import Axiom.Extensionality.Propositional
open import Function
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Data.Maybe hiding (_>>=_)

open import Data.Bool
open import Data.Product
open import Data.Empty
open import Free
open import FreeND
open import Effect
open import Level using (Level)

-- Include functional extensionality
private
  variable
    level : Level

postulate
  -- functional extensionality: if equal inputs produce equal outputs then the functions are equal
  funext : Extensionality level level

-- Define the non-determinism monad as a free monad over the choice effect
ND = NDFree

infixr 6 _~⟨_⟩_
infixr 6 _~⟨⟩_
infix 6 _~_
infix 7 _∎
infix 5 _⇓_

-- Convergence rules
data _⇓_ {A : Set} : ND A → A → Set where
  -- ret x converges to x
  -- Args: a proof that nd ≡ ret x 
  conv-ret : (x : A) → pure x ⇓ x
  -- p ⊕ q converges to v if p converges to v
  -- Args: proof p converges to x, q: ND A, proof that nd = p ⊕ q
  conv-l : ∀{p} {x} {nd} → p ⇓ x → (q : ND A) → nd ≡ p ⊕ q → nd ⇓ x
  -- p ⊕ q converges to v if q converges to v
  -- Args: p: ND A, proof q converges to x, proof of that nd = p ⊕ q
  conv-r : ∀{q} {x} {nd} → (p : ND A) → q ⇓ x → nd ≡ p ⊕ q → nd ⇓ x

-- p and q are bisimilar if they converge to the same value for all possible values
record _~_  {A : Set} (p q : ND A) : Set where
  constructor mk~
  field
    ~conv-l : ∀ {v} → p ⇓ v → q ⇓ v
    ~conv-r : ∀ {v} → q ⇓ v → p ⇓ v
open _~_ public

-- basic properties of _~_

~refl  : ∀ {A} {a : ND A} → a ~ a
~refl = mk~ id id

~trans : ∀ {A} {a b c : ND A}
  (eq : a ~ b) (eq' : b ~ c) → a ~ c
~trans eq eq' = mk~ ( λ c → ~conv-l eq' (~conv-l eq c))
                    ( λ c → ~conv-r eq (~conv-r eq' c))

~eq-refl : ∀ {A} {a b : ND A} → a ≡ b → a ~ b
~eq-refl refl = ~refl

~symm : ∀ {A} {a b : ND A}
  (eq : a ~ b) → b ~ a
~symm eq = mk~ (~conv-r eq) (~conv-l eq)

-- if p converges to v implies that p' converges to v
-- and the same for q and q'
-- then p ⊕ q converges to v implies that p' ⊕ q' converges to v
conv-cong : ∀ {A} {v} {p q p' q' : ND A} →
  (p ⇓ v → p' ⇓ v) → (q ⇓ v → q' ⇓ v) → p ⊕ q ⇓ v → p' ⊕ q' ⇓ v
conv-cong f g (conv-l c q x₁) with ⊕-inj x₁
... | (refl , refl) = conv-l (f c) _ refl
conv-cong f g (conv-r p' c x₁) with ⊕-inj x₁
... | (refl , refl) = conv-r _ (g c) refl

-- conv-cong : ∀ {A} {v} {p q p' q' : ND A} →
--   (p ⇓ v → p' ⇓ v) → (q ⇓ v → q' ⇓ v) → p ⊕ q ⇓ v → p' ⊕ q' ⇓ v
-- conv-cong f g (conv-l c _) =  conv-l (f c) _
-- conv-cong f g (conv-r _ c) =  conv-r _ (g c)

-- if p ~ p' and q ~ q' then p ⊕ q ~ p' ⊕ q'
plus-cong : ∀ {A} {p q p' q' : ND A} → p ~ p' → q ~ q' → p ⊕ q ~ p' ⊕ q'
plus-cong eq eq' = mk~ (conv-cong (~conv-l eq) (~conv-l eq'))
                        (conv-cong (~conv-r eq) (~conv-r eq'))

plus-cong-r : ∀ {A} {p q q' : ND A} → q ~ q' → p ⊕ q ~ p ⊕ q'
plus-cong-r eq = plus-cong ~refl eq

plus-cong-l : ∀ {A} {p q p' : ND A} → p ~ p' → p ⊕ q ~ p' ⊕ q
plus-cong-l eq = plus-cong  eq ~refl


_~⟨_⟩_ : ∀ {A : Set} (x : ND A) → ∀ {y : ND A} {z : ND A} → x ~ y → y ~ z → x ~ z
_~⟨_⟩_ {_} x r eq =  ~trans r eq

_~⟨⟩_ : ∀ {A : Set} (x : ND A) → ∀ {y : ND A} → x ~ y → x ~ y
_~⟨⟩_  x eq = eq

_∎ : ∀ {A : Set} (x : ND A) → x ~ x
_∎  x = ~refl

-- fold over an if statements distributes the if over the folds
fold-if-distr : ∀ {A B : Set} {E : Effect} (f : A → B) (g : Alg E B) b x y
              → (fold f g (if b then x else y))
                ≡ (if b then (fold f g x) else (fold f g y))

fold-if-distr f g false x y = refl
fold-if-distr f g true x y = refl

-- definition of p ⊕ q equals its definition
distr-plus : ∀ {A} {p q : ND A} →
  (impure (ChoiceOp , (λ b → if b then p else q))) ≡ p ⊕ q
distr-plus = refl

-- (p ⊕ q >>= f) ≡ (p >>= f) ⊕ (q >>= f)
-- since m >>= f = fold f impure m, and a = p ⊕ vx, we can use fold-if-distr
distr-plus-bind : ∀ {A B} {f : A → ND B} {p q : ND A} →
  (impure (ChoiceOp , (λ b → if b then p else q)) >>= f) ≡ (p >>= f) ⊕ (q >>= f)
distr-plus-bind {f = f} = (cong (λ X → impure (ChoiceOp , X)) (funext (λ x → fold-if-distr f impure x _ _)))

~distr-plus-bind : ∀ {A B} {f : A → ND B} {p q : ND A} →
  ((p ⊕ q) >>= f) ~ (p >>= f) ⊕ (q >>= f)
~distr-plus-bind {f = f} = ~eq-refl (distr-plus-bind)

~distr-plus-bind' : ∀ {A B} {f : A → ND B} {p q : ND A} →
  ((p >>= f) ⊕ (q >>= f)) ~ ((p ⊕ q) >>= f)
~distr-plus-bind' {f = f} = ~eq-refl (sym (distr-plus-bind))

-- If a converges to v, and f (v) converges to w, than a >>= f converges to w
bind-cong-conv : ∀ {A B} {a : ND A} {f : A → ND B} {v : A} {w : B}
 → (a ⇓ v) → f v ⇓ w → (a >>= f) ⇓ w
-- a = pure x
bind-cong-conv {a = pure x} (conv-ret .x) d = d
-- a = p ⊕ q, where p converges to v
bind-cong-conv {a = impure (ChoiceOp , .(λ b → if b then _ else q))} {f = f} (conv-l c q refl) d
  = conv-l
      -- show that left side converges to w
      (bind-cong-conv c d)
      -- given an instance of ND B
      (q >>= f)
      -- show that (a >>= f) ≡ (p >>= f) ⊕ (q >>= f)
      (distr-plus-bind)
-- a = p ⊕ q, where q converges to v
bind-cong-conv {a = impure (ChoiceOp , .(λ b → if b then p else _))} {f = f} (conv-r p c refl) d
  = conv-r
      -- give an instance of ND B
      (p >>= f)
      -- show that the right side converges to w
      (bind-cong-conv c d)
      -- show that (a >>= f) ≡ (p >>= f) ⊕ (q >>= f)
      (distr-plus-bind)

Bool-eta : ∀ {A : Set} (f : Bool → A) → f ≡ λ b → if b then f true else f false
Bool-eta f = funext λ {true → refl ; false → refl }

plus-extraction :
  ∀ {A : Set} {cont : Effect.Ret NDEffect ChoiceOp → Free NDEffect A}
  → ∃ (λ p → ∃ (λ q → p ⊕ q ≡ impure (ChoiceOp , cont)))
plus-extraction {cont = cont} = (cont true) , (cont false) , impure-inj' (sym (Bool-eta cont))

-- a >>= f converges to w implies there exists a v such that a converges to v and f v converges to w
bind-cong-conv' : ∀ {A B} {a : ND A} {f : A → ND B} {w : B} 
                  → (a >>= f) ⇓ w → ∃[ v ] ((a ⇓ v) × f v ⇓ w)

-- case pure xa : (pure xa >> f) converges to w, so xa converges to xa and f v converges to w
bind-cong-conv' {a = pure xa} c = xa , conv-ret _ , c
-- case (a >> f) = (p ⊕ q) >> f, where (p << f) converges to w
-- However, we instead get the case (a >> f) = p ⊕ q converges to w, where p converges to w.
bind-cong-conv' {a = impure (ChoiceOp , k)} {f = f} (conv-l {p = p} c q x)
  with f-inj (impure-inj x) true
...  | refl with bind-cong-conv' {a = k true} {f = f} c
...            | (v' , r' , t')
                 =   _
                   , conv-l r'
                       (k false)
                       (cong (impure ∘ (ChoiceOp ,_)) (Bool-eta k))
                   , t'
bind-cong-conv' {a = impure (ChoiceOp , k)} {f = f} (conv-r {q = q} p c x)
  with f-inj (impure-inj x) false
...  | refl with bind-cong-conv' {a = k false} {f = f} c
... | (v' , r' , t')
    = _
    , conv-r (k true) r' (cong (impure ∘ (ChoiceOp ,_)) (Bool-eta k))
    , t'

bind-cong : ∀ {A B}  {a b : ND A} (eq : a ~ b)
            {k l : A → ND B} (h : ∀ a → (k a) ~ (l a)) →
            (a >>= k) ~ (b >>= l)

bind-cong {a = a} {b} (mk~ le ri) {k} {l} h = mk~  ri'  le'
  where ri' : ∀ {v} → (a >>= k) ⇓ v → (b >>= l) ⇓ v
        ri' c with bind-cong-conv' {a = a} c
        ... | w , c1 , c2 = bind-cong-conv (le c1) (~conv-l (h w) c2)
        le' : ∀ {v} → (b >>= l) ⇓ v → (a >>= k) ⇓ v
        le' c with bind-cong-conv' {a = b} c
        ... | w , c1 , c2 = bind-cong-conv (ri c1) (~conv-r (h w) c2)

bind-cong-l : ∀ {A B}  {a b : ND A} (eq : a ~ b)
            (k : A → ND B) →
            (a >>= k) ~ (b >>= k)
bind-cong-l eq _ = bind-cong  eq  (λ _ → ~refl)

bind-cong-r : ∀ {A B}  (a : ND A)
              {k l : A → ND B} (h : ∀ a → (k a) ~ (l a)) →
              (a >>= k) ~ (a >>= l)
bind-cong-r a f = bind-cong {a = a}  ~refl f


-- ----------------
-- -- monad laws --
-- ----------------

impure-zero-is-zero : ∀ {A} {k : Effect.Ret NDEffect ZeroOp → Free NDEffect A} → impure (ZeroOp , k) ≡ zero
impure-zero-is-zero {k = k} = impure-inj' {o = ZeroOp} {k = k} (funext λ ())

fold-zero : ∀ {A B : Set} {f : A → ND B} → fold f impure zero ≡ zero
fold-zero {A} {B} {f} = impure-inj' {o = ZeroOp} (funext λ ())

fold-zero-equiv : ∀ {A} {k1 k2 : Effect.Ret NDEffect ZeroOp → Free NDEffect A} → impure (ZeroOp , k1) ≡ impure (ZeroOp , k2)
fold-zero-equiv {A} {k1} {k2} with (impure-zero-is-zero {k = k1}) | (impure-zero-is-zero {k = k2})
... | refl | refl = refl

~zero-refl : ∀ {A : Set} {k1 k2 : Effect.Ret NDEffect ZeroOp → Free NDEffect A} → impure (ZeroOp , k1) ~ impure (ZeroOp , k2)
~zero-refl {k1 = k1} {k2 = k2} with (fold-zero-equiv {k1 = k1} {k2 = k2})
... | refl = ~refl


choice-op-equiv-conv : ∀ {A} {k1 k2 : Effect.Ret NDEffect ChoiceOp → Free NDEffect A}
  → k1 ≡ k2
  → impure (ChoiceOp , k1) ~ impure (ChoiceOp , k2)
choice-op-equiv-conv {A} {k1} {k2} refl = ~refl

~choice-op-cong : ∀ {A} {k1 k2 : Effect.Ret NDEffect ChoiceOp → Free NDEffect A}
  → (k1 true) ~ (k2 true)
  → (k1 false) ~ (k2 false)
  → impure (ChoiceOp , k1) ~ impure (ChoiceOp , k2)
~choice-op-cong {A} {k1} {k2} eq1 eq2 with plus-extraction {cont = k1} | plus-extraction {cont = k2}
... | p1 , q1 , refl | p2 , q2 , refl = plus-cong eq1 eq2

-- monad law: bind is associative
bind-assoc : ∀{A B C} (m : ND A) {k : A → ND B} {l : B → ND C}
                      → ((m >>= k) >>= l) ~ (m >>= λ a → k a >>= l)
bind-assoc (pure x) = ~refl
bind-assoc (impure (ZeroOp , cont)) = ~zero-refl
bind-assoc (impure (ChoiceOp , cont)) = ~choice-op-cong (bind-assoc (cont true)) (bind-assoc (cont false))


bind-unit-r : ∀ {A} (p : ND A)  → (p >>= pure) ~ p
bind-unit-r (pure x) =  ~refl
bind-unit-r (impure (ZeroOp , cont)) =  ~zero-refl
bind-unit-r (impure (ChoiceOp , cont)) = ~choice-op-cong (bind-unit-r (cont true)) (bind-unit-r (cont false))

bind-unit-l : ∀ {A B} {x : A} (f : A → ND B)  → (pure x >>= f) ~ f x
bind-unit-l p =  ~refl

-- -- -- lemmas --

-- zero ⊕ p ⇓ v implies p ⇓ v because zero does not converge to any value
conv-plus-unit-l : ∀ {A} {p : ND A} {v : A} → zero ⊕ p ⇓ v → p ⇓ v
conv-plus-unit-l (conv-r {q = q} p c x) with f-inj (impure-inj x) false
... | refl = c
conv-plus-unit-l (conv-l {p = p} c q x) with f-inj (impure-inj x) true
conv-plus-unit-l (conv-l {p = .(impure (ZeroOp , (λ ())))} (conv-l c _ ()) q x) | refl 
conv-plus-unit-l (conv-l {p = .(impure (ZeroOp , (λ ())))} (conv-r p c ()) q x) | refl

-- p ⊕ zero ⇓ v implies p ⇓ v because zero does not converge to any value
conv-plus-unit-r : ∀ {A} {p : ND A} {v : A} → p ⊕ zero ⇓ v → p ⇓ v
conv-plus-unit-r (conv-l c q x) with f-inj (impure-inj x) true
... | refl = c
conv-plus-unit-r (conv-r p arg x) with f-inj (impure-inj x) false
conv-plus-unit-r (conv-r p (conv-l arg q ()) x) | refl
conv-plus-unit-r (conv-r p (conv-r _ arg ()) x) | refl

-- associativity of plus
conv-plus-assoc : ∀ {A} {p q r : ND A} {v : A}
                  → (p ⊕ q) ⊕ r ⇓ v
                  → p ⊕ (q ⊕ r) ⇓ v
conv-plus-assoc (conv-l (conv-ret x) q eq) with f-inj (impure-inj eq) true
... | ()
conv-plus-assoc (conv-l  {p = pq} (conv-l {p = p} cond q eqp-pq) r eqp-pq-r) with (⊕-inj eqp-pq-r)
... | refl , refl with (⊕-inj eqp-pq)
... | refl , refl = conv-l cond (q ⊕ r) refl

conv-plus-assoc (conv-l (conv-r {q = q} p cond eqp-pq) r eqp-pq-r) with (⊕-inj eqp-pq-r)
... | refl , refl with (⊕-inj eqp-pq)
... | refl , refl = conv-r p (conv-l cond r refl) refl
conv-plus-assoc {p = p} {q = q} {r = r} (conv-r pq cond eqp-pq-r) with (⊕-inj eqp-pq-r)
... | refl , refl = conv-r p (conv-r q cond refl) refl




conv-plus-assoc' : ∀  {A} {p q r : ND A} {v : A}
                   → p ⊕ (q ⊕ r) ⇓ v
                   → (p ⊕ q) ⊕ r ⇓ v
                   
-- p converges to v
conv-plus-assoc' {p = p} {q = q} {r = r} (conv-l cond qr eqp-p-qr) with (⊕-inj eqp-p-qr)
... | refl , refl = conv-l (conv-l cond q refl) r refl

conv-plus-assoc' (conv-r p (conv-ret _) eq-p-qr) with f-inj (impure-inj eq-p-qr) false
... | ()
-- q converges to v
conv-plus-assoc' (conv-r p (conv-l cond q eq-qr) eq-p-qr) with (⊕-inj eq-p-qr)
... | refl , refl with (⊕-inj eq-qr)
... | refl , refl = conv-l (conv-r _ cond refl) _ refl

-- r converges to v
conv-plus-assoc' (conv-r p (conv-r r cond eq-qr) eq-p-qr) with (⊕-inj eq-p-qr)
... | refl , refl with (⊕-inj eq-qr)
... | refl , refl = conv-r _ cond refl


conv-plus-idem : ∀  {A} {v : A} {p : ND A} → p ⊕ p ⇓ v → p ⇓ v
conv-plus-idem (conv-l c _ eq-pp) with (⊕-inj eq-pp)
... | refl , refl = c
conv-plus-idem (conv-r _ c eq-qq) with (⊕-inj eq-qq)
... | refl , refl = c

conv-plus-idem' : ∀  {A} {v : A} {p : ND A} → p ⇓ v → p ⊕ p ⇓ v
conv-plus-idem' c = conv-l c _ refl



conv-plus-comm : ∀  {A} {v : A} {p q : ND A} → p ⊕ q ⇓ v → q ⊕ p ⇓ v
conv-plus-comm (conv-l c _ eq-pp) with (⊕-inj eq-pp)
... | refl , refl = conv-r _ c refl
conv-plus-comm (conv-r _ c eq-qq) with (⊕-inj eq-qq)
... | refl , refl = conv-l c _ refl


-- --------------------------
-- -- non-determinism laws --
-- --------------------------

plus-unit-l : ∀  {A} {p : ND A} → zero ⊕ p ~ p
plus-unit-l = mk~ conv-plus-unit-l ( λ c → conv-r _ c refl)


plus-unit-r : ∀  {A} {p : ND A} → p ⊕ zero ~ p
plus-unit-r = mk~ conv-plus-unit-r ( λ c → conv-l c _ refl)


plus-assoc : ∀  {A} {p q r : ND A} → (p ⊕ q) ⊕ r ~ p ⊕ (q ⊕ r)
plus-assoc = mk~ conv-plus-assoc conv-plus-assoc'


plus-idem : ∀  {A} (p : ND A) → p ⊕ p ~ p
plus-idem p = mk~ conv-plus-idem conv-plus-idem'


plus-comm : ∀  {A} {p q : ND A} → p ⊕ q ~ q ⊕ p
plus-comm = mk~ conv-plus-comm conv-plus-comm

plus-distr : ∀  {A B} {p q : ND A} {f : A → ND B}  → ((p ⊕ q) >>= f) ~ (p >>= f) ⊕ (q >>= f)
plus-distr = ~choice-op-cong ~refl ~refl

zero-bind : ∀  {A B} {f : A → ND B} → (zero >>= f) ~ zero
zero-bind = ~zero-refl

-- TODO: Without needing terminating
-- {-# TERMINATING #-}
plus-distr-dup : ∀  {A B} {p : ND A} {q : ND B} {f : A → ND B}
  → (p >>= f) ⊕ q ~ (p >>= λ x → f x ⊕ q) ⊕ q
plus-distr-dup  {p = pure x} {q} {f} =
  f x ⊕ q
  ~⟨ plus-cong-r (~symm (plus-idem q)) ⟩
  f x ⊕ (q ⊕ q)
  ~⟨  ~symm plus-assoc ⟩
  f x ⊕ q ⊕ q
  ∎

plus-distr-dup {p = impure (ZeroOp , cont)} = ~choice-op-cong ~zero-refl ~refl
plus-distr-dup {p = impure (ChoiceOp , cont)} {q} {f} with plus-extraction {cont = cont}
... | p1 , p2 , refl = ((p1 ⊕ p2) >>= f) ⊕ q
  ~⟨ plus-cong-l (~distr-plus-bind) ⟩
  ((p1 >>= f) ⊕ (p2 >>= f)) ⊕ q
  ~⟨ plus-assoc ⟩
  (p1 >>= f) ⊕ ((p2 >>= f) ⊕ q)
  ~⟨ plus-cong-r (plus-distr-dup {p = p2}) ⟩
  (p1 >>= f) ⊕ ((p2 >>= (λ x → f x ⊕ q)) ⊕ q)
  ~⟨  plus-cong-r plus-comm ⟩
  (p1 >>= f) ⊕ (q ⊕ (p2 >>= (λ x → f x ⊕ q)))
  ~⟨  ~symm plus-assoc ⟩
  (p1 >>= f) ⊕ q ⊕ (p2 >>= (λ x → f x ⊕ q))
  ~⟨ plus-cong-l (plus-distr-dup {p = p1}) ⟩
  ((p1 >>= (λ x → f x ⊕ q)) ⊕ q) ⊕ (p2 >>= (λ x → f x ⊕ q))
  ~⟨ plus-cong-l plus-comm ⟩
  (q ⊕ (p1 >>= (λ x → f x ⊕ q))) ⊕ (p2 >>= (λ x → f x ⊕ q))
  ~⟨ plus-assoc ⟩
  q ⊕ ((p1 >>= (λ x → f x ⊕ q)) ⊕ (p2 >>= (λ x → f x ⊕ q)))
  ~⟨  plus-comm ⟩
  (p1 >>= (λ x → f x ⊕ q)) ⊕ (p2 >>= (λ x → f x ⊕ q)) ⊕ q
  ~⟨ plus-cong-l (~distr-plus-bind') ⟩
   ((p1 ⊕ p2) >>= λ x → f x ⊕ q) ⊕ q
  ∎

-- TODO: Without needing terminating
-- {-# TERMINATING #-}
interchange : ∀  {A B} {p : ND A} {q : ND B} {f : A → ND B} → (∃[ v ] p ⇓ v)
  → (p >>= f) ⊕ q ~ (p >>= λ x → f x ⊕ q)
interchange {p = pure x} _ =  ~refl
interchange {p = impure (ZeroOp , cont)} (v , conv-l x q ())
interchange {p = impure (ZeroOp , cont)} (v , conv-r p x ())

interchange {p = impure (ChoiceOp , cont)} {q} {f} (v , conv-l {p = p1'} cond p2' eq-pq) with plus-extraction {cont = cont}
... | p1 , p2 , refl with (⊕-inj eq-pq)
... | refl , refl = 
  ((p1 ⊕ p2) >>= f) ⊕ q
  ~⟨ plus-cong-l (~distr-plus-bind) ⟩
  ((p1 >>= f) ⊕ (p2 >>= f) ⊕ q)
  ~⟨ plus-assoc ⟩
  ((p1 >>= f) ⊕ ((p2 >>= f) ⊕ q))
  ~⟨ plus-cong-r (plus-distr-dup {p = p2}) ⟩
  ((p1 >>= f) ⊕ ((p2 >>= λ x → f x ⊕ q) ⊕ q))
  ~⟨ plus-cong-r plus-comm ⟩
  ((p1 >>= f) ⊕ (q ⊕ (p2 >>= λ x → f x ⊕ q)))
  ~⟨ ~symm plus-assoc ⟩
  (((p1 >>= f) ⊕ q) ⊕ (p2 >>= λ x → f x ⊕ q))
  ~⟨  plus-cong-l (interchange (v , cond)) ⟩
  ((p1 >>= λ x → f x ⊕ q) ⊕ (p2 >>= λ x → f x ⊕ q))
  ~⟨ ~distr-plus-bind' ⟩
  ((p1 ⊕ p2) >>= (λ x → f x ⊕ q))
  ∎
interchange {p = impure (ChoiceOp , cont)} {q} {f} (v , conv-r {q = p2'} p1' cond eq-pq) with plus-extraction {cont = cont}
... | p1 , p2 , refl with (⊕-inj eq-pq)
... | refl , refl = 
  ((p1 ⊕ p2) >>= f) ⊕ q
  ~⟨ plus-cong-l (~distr-plus-bind) ⟩
  ((p1 >>= f) ⊕ (p2 >>= f) ⊕ q)
  ~⟨ plus-cong-l plus-comm ⟩
  ((p2 >>= f) ⊕ (p1 >>= f) ⊕ q)
  ~⟨ plus-assoc ⟩
  ((p2 >>= f) ⊕ ((p1 >>= f) ⊕ q))
  ~⟨ plus-cong-r (plus-distr-dup {p = p1}) ⟩
  ((p2 >>= f) ⊕ ((p1 >>= λ x → f x ⊕ q) ⊕ q))
  ~⟨ plus-cong-r plus-comm ⟩
  ((p2 >>= f) ⊕ (q ⊕ (p1 >>= λ x → f x ⊕ q)))
  ~⟨ ~symm plus-assoc ⟩
  ((p2 >>= f) ⊕ q ⊕ (p1 >>= λ x → f x ⊕ q))
  ~⟨  plus-cong-l (interchange (v , cond)) ⟩
  ((p2 >>= λ x → f x ⊕ q) ⊕ (p1 >>= λ x → f x ⊕ q))
  ~⟨ plus-comm ⟩
  ((p1 >>= λ x → f x ⊕ q) ⊕ (p2 >>= λ x → f x ⊕ q))
  ~⟨ ~distr-plus-bind' ⟩
  ((p1 ⊕ p2) >>= (λ x → f x ⊕ q))
  ∎


-- Pattern matching


match : ∀ {A B C : Set} → (A → Maybe B) → ND C → (B → ND C) → A → ND C
match m d f a with m a
... | just x =  f x
... | nothing = d

getJust : ∀ {A B : Set} → ND B → (A → ND B) → Maybe A → ND B
getJust = match id


match-assoc : ∀{A B C D} (c : A → Maybe B) (m : ND A) {d : ND C}
               {f : B → ND C}{g : C → ND D} →
               ((m >>= match c d f) >>= g) ~ (m >>= match c (d >>= g) (λ x → f x >>=  g))
match-assoc {A} {B} c m {d} {f} {g} =
  ~trans (bind-assoc m) ( bind-cong-r m (λ x → cases c x ))
  where 
  cases : (c : A → Maybe B) (x : A) →
          (match c d f x >>= g) ~ (match c (d >>= g) (λ y → f y >>= g) x)
  cases c x with c x
  ... | just y  =  ~refl
  ... | nothing =  ~refl

getJust-assoc : ∀{B C D} (m : ND (Maybe B)) {d : ND C}
               {f : B → ND C}{g : C → ND D} →
               ((m >>= getJust d f) >>= g) ~ (m >>= getJust (d >>= g) (λ x → f x >>= g))
getJust-assoc = match-assoc id


match-cong-default : ∀{A B C} (c : A → Maybe B) (m : ND A)
  {d : ND C} {e : ND C} {f : B → ND C}
               (h : d ~ e) →
               (m >>= match c d f) ~ (m >>= match c e f)

match-cong-default {A} c m {d} {e} {f} h =  bind-cong-r m   cases
  where cases : (a : A) → (match c d f a) ~ (match c e f a)
        cases a with c a
        ...| just x =  ~refl
        ...| nothing = h


getJust-cong-default : ∀{B C} (m : ND (Maybe B))
  {d : ND C} {e : ND C} {f : B → ND C}
               (h : d ~ e) →
               (m >>= getJust d f) ~ (m >>= getJust e f)
getJust-cong-default = match-cong-default id


match-cong : ∀{A B C} (c : A → Maybe B) (m : ND A) {d : ND C}
               {f : B → ND C} {g : B → ND C}
               (h : ∀ x → f x ~ g x) →
               (m >>= match c d f) ~ (m >>= match c d g)
match-cong {A} c m {d} {f} {g} e =  bind-cong-r m  cases
  where cases : (x : A) → match c d f x ~ match c d g x
        cases x with c x
        ...| just y =  e y
        ...| nothing =  ~refl

getJust-cong : ∀{B C} (m : ND (Maybe B)) {d : ND C}
               {f : B → ND C} {g : B → ND C}
               (h : ∀ x → f x ~ g x) →
               (m >>= getJust d f) ~ (m >>= getJust d g)
getJust-cong = match-cong id

match-distr :  ∀{A B C} (c : A → Maybe B)
            {p q : ND C} {f : B → ND C} a
            → match c p f a ⊕ q ~ match c (p ⊕ q) (λ x → f x ⊕ q) a
match-distr c a with c a
... | nothing = ~refl
... | just x = ~refl


match-interchange :  ∀{A B C} (c : A → Maybe B) {m : ND A}
            {p q : ND C} {f : B → ND C} → ∃[ v ] m ⇓ v
            → (m >>= λ a → match c p f a) ⊕ q ~ (m >>= λ a → match c (p ⊕ q) (λ x → f x ⊕ q) a)
match-interchange c {m} d = ~trans (interchange d) (bind-cong-r m ( λ a → match-distr c a))


getJust-interchange :  ∀{B C} {m : ND (Maybe B)}
            {p q : ND C} {f : B → ND C} → ∃[ v ] m ⇓ v
            → (m >>= λ a → getJust p f a) ⊕ q ~ (m >>= λ a → getJust (p ⊕ q) (λ x → f x ⊕ q) a)
getJust-interchange = match-interchange id


-- -- reasoning about convergence

pos-ret : ∀ {A} {x : A} → ∃[ v ] ret x ⇓ v
pos-ret {x = x} = x , conv-ret x

pos-plus-l : ∀ {A} {p q : ND A} → ∃[ v ] p ⇓ v → ∃[ v ] p ⊕ q ⇓ v
pos-plus-l (v , c) = v , conv-l c _ refl

pos-bind : ∀ {A B} (p : ND A) {f : A → ND B} → ∃[ v ] p ⇓ v → (∀ w → ∃[ v ] f w ⇓ v) → ∃[ v ] (p >>= f) ⇓ v
pos-bind p (v , c) f with f v
...| w , d =  w , bind-cong-conv  c d

pos-getJust : ∀ {A B} (p : ND B) {f : A → ND B} (m : Maybe A) → ∃[ v ] p ⇓ v → (∀ w → ∃[ v ] f w ⇓ v) → ∃[ v ] (getJust p f m) ⇓ v
pos-getJust p nothing c f = c
pos-getJust p (just x) c f = f x
