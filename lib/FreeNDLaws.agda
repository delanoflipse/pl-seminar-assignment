open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Bool
open import Data.Product
open import Free
open import FreeND
open import Effect
open import Level using (Level)

ND = NDFree

infixr 6 _~⟨_⟩_
infixr 6 _~⟨⟩_
infix 6 _~_
infix 7 _∎
infix 5 _⇓_

-- convergence rules for ND
data _⇓_ {A : Set} (nd : ND A) (x : A) : Set where
  -- ret x converges to x
  -- Args: a proof that nd ≡ ret x 
  conv-ret : nd ≡ ret x → nd ⇓ x
  -- p ⊕ q converges to v if p converges to v
  -- Args: proof p converges to x, q: ND A, proof that nd = p ⊕ q
  conv-l : ∀ {p} → p ⇓ x → (q : ND A) → nd ≡ (p ⊕ q) → nd ⇓ x
  -- p ⊕ q converges to v if q converges to v
  -- Args: p: ND A, proof q converges to x, proof of that nd = p ⊕ q
  conv-r : ∀ {q} → (p : ND A) → q ⇓ x → nd ≡ (p ⊕ q) → nd ⇓ x

-- data _⇓_ {A : Set} : ND A → A → Set where
--   conv-ret : (x : A) → ret x ⇓ x
--   conv-l : ∀{p} {x} → p ⇓ x → (q : ND A) → p ⊕ q ⇓ x
--   conv-r : ∀{q} {x} → (p : ND A) → q ⇓ x → p ⊕ q ⇓ x

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

-- if p = p' and q = q' then p ⊕ q = p' ⊕ q'
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


private
  variable
    ℓ0 : Level

postulate
  -- fold over an if statements distributes the if over the folds
  fold-if-distr : ∀ {A B : Set} {E : Effect} (f : A → B) (g : Alg E B) b x y
                → (fold f g (if b then x else y))
                  ≡ (if b then (fold f g x) else (fold f g y))

  -- functional extensionality: if equal inputs produce equal outputs then the functions are equal
  funext : Extensionality ℓ0 ℓ0

distr-plus : ∀ {A} {p q : ND A} →
  (impure (ChoiceOp , (λ b → if b then p else q))) ≡ p ⊕ q
distr-plus = refl

-- (p ⊕ q >>= f) ≡ (p >>= f) ⊕ (q >>= f)
-- since m >>= f = fold f impure m, and a = p ⊕ vx, we can use fold-if-distr
distr-plus-bind : ∀ {A B} {f : A → ND B} {p q : ND A} →
  (impure (ChoiceOp , (λ b → if b then p else q)) >>= f) ≡ (p >>= f) ⊕ (q >>= f)
distr-plus-bind {f = f} = (cong (λ X → impure (ChoiceOp , X)) (funext (λ x → fold-if-distr f impure x _ _)))

-- If a converges to v, and f (v) converges to w, than a >>= f converges to w
bind-cong-conv : ∀ {A B} {a : ND A} {f : A → ND B} {v : A} {w : B}
 → (a ⇓ v) → f v ⇓ w → (a >>= f) ⇓ w
-- a = pure x
bind-cong-conv {a = pure x} (conv-ret refl) d = d
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

{-
bind-cong-conv : ∀ {A B} {a : ND A} {f : A → ND B} {v : A} {w : B}
 → (a ⇓ v) → f v ⇓ w → (a >>= f) ⇓ w

-- Given a is pure (x: A), the case that a converges to v, and f v converges to w
bind-cong-conv {a = pure x} (conv-ret refl) d = d

-- bind-cong-conv {a = pure x} (conv-ret r) d = subst r {!   !}

bind-cong-conv (conv-l c q x) d with impure-inj x
... | x = ?
-- bind-cong-conv (conv-l c q refl) d = conv-l x1 x2 refl where
--   x1 = ?
--   x2 = ?
bind-cong-conv (conv-r p c refl) d = {!   !}
-- bind-cong-conv {a = pure x} (conv-ret refl) d = {!   !}
-- bind-cong-conv {a = impure (ChoiceOp , k)} d = {!   !}
-- bind-cong-conv {a = impure (ChoiceOp , k)} (conv-l c _ x₁) d with f-inj (impure-inj x₁)
-- ... | ff = {!   !}
-- bind-cong-conv {a = impure (ChoiceOp , k)} (conv-l c vx x₁) d with ⊕-inj x₁
-- ... | (r1 , r2) = ?
-- bind-cong-conv {a = impure (ChoiceOp , k)} (conv-r _ c x₁) d = {!   !}
-- Original:
-- https://agda.readthedocs.io/en/v2.6.1/language/function-definitions.html#dot-patterns
-- bind-cong-conv {a = a1 ⊕ a2} (conv-l c .a2) d = conv-l (bind-cong-conv c d) _
-- bind-cong-conv {a = a1 ⊕ a2} (conv-r .a1 c) d = conv-r _ (bind-cong-conv c d)
-}

-- postulate
--   distr-plus-bind-left' : ∀ {A B} {f : A → ND B} {p q : ND B} {k} →
--     (impure (ChoiceOp , k) >>= f) ≡ (p ⊕ q) → {p' : ND A} → ∃[ p' ] (p' >>= f ≡ p)

Bool-eta : ∀ {A : Set} (f : Bool → A) → f ≡ λ b → if b then f true else f false
Bool-eta f = funext λ {true → refl ; false → refl }

-- a >>= f converges to w implies there exists a v such that a converges to v and f v converges to w
bind-cong-conv' : ∀ {A B} {a : ND A} {f : A → ND B} {w : B} 
                  → (a >>= f) ⇓ w → ∃[ v ] ((a ⇓ v) × f v ⇓ w)

-- case pure xa : (pure xa >> f) converges to w, so xa converges to xa and f v converges to w
bind-cong-conv' {a = pure xa} c = xa , conv-ret refl , c
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

{-
-- bind-cong-conv' {a = impure (ChoiceOp , k)} {f = f} (conv-l {p = .(_ >>= f)} c .(_ >>= f) x) = _ , {!   !}
-- bind-cong-conv' {a = impure (ChoiceOp , .(λ x → fold f impure (λ b → if b then (p' >>= f) else ('q >>= f))))} {f = f} (conv-l {p = p} c q x) = _ , {!   !}
-- bind-cong-conv' {a = impure (ChoiceOp , k)} {f = f} (conv-l {p = p} c q x) = ?
-- bind-cong-conv' {a = pure x} c = x , ((conv-ret refl) , c)

-- bind-cong-conv' {a = impure (ChoiceOp , .(λ _ → if _ then _ else _))} (conv-l c .(_ >>= _) refl) with bind-cong-conv' {a = _} c
-- ... | v' , d1 , d2 =  v' , {!   !} , d2
-- bind-cong-conv' {a = impure (ChoiceOp , .(λ _ → if _ then _ else _))} (conv-r .(_ >>= _) c refl) with bind-cong-conv' {a = _} c
-- ... | v' , d1 , d2 =  v' , conv-r _ _ _ , d2

-- Original:
-- bind-cong-conv' {a = ret x} c = x , (conv-ret x , c)
-- bind-cong-conv' {a = a1 ⊕ a2} (conv-l c .(a2 Bind.>>= _)) with bind-cong-conv' {a = a1} c
-- ... | v' , d1 , d2 = v' , conv-l d1 a2 , d2
-- bind-cong-conv' {a = a1 ⊕ a2} (conv-r .(a1 Bind.>>= _) c) with bind-cong-conv' {a = a2} c
-- ... | v' , d1 , d2 = v' , conv-r a1 d1 , d2
-}

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

bind-assoc : ∀{A B C}(m : ND A)
                 {k : A → ND B} {l : B → ND C} →
                 ((m >>= k) >>= l) ~ (m >>= λ a → k a >>= l)
bind-assoc (pure x) = ~refl
bind-assoc (impure (ZeroOp , k)) = {!   !}
bind-assoc (impure (ChoiceOp , snd)) = {!   !}
-- bind-assoc (ret x) =  ~refl
-- bind-assoc zero =  ~refl
-- bind-assoc (m ⊕ m') = plus-cong (bind-assoc  m) (bind-assoc m')


-- bind-unit-r : ∀ {A} (p : ND A)  → (p >>= return) ~ p
-- bind-unit-r (ret x) =  ~refl
-- bind-unit-r zero =  ~refl
-- bind-unit-r (p ⊕ q) = plus-cong (bind-unit-r p) (bind-unit-r q)

-- bind-unit-l : ∀ {A B} {x : A} (f : A → ND B)  → (return x >>= f) ~ f x
-- bind-unit-l p =  ~refl


-- -- -- lemmas --

-- conv-plus-unit-l : ∀ {A} {p : ND A} {v : A} → zero ⊕ p ⇓ v → p ⇓ v
-- conv-plus-unit-l (conv-r .zero c) = c

-- conv-plus-unit-r : ∀ {A} {p : ND A} {v : A} → p ⊕ zero ⇓ v → p ⇓ v
-- conv-plus-unit-r (conv-l c .zero) = c


-- conv-plus-assoc : ∀ {A} {p q r : ND A} {v : A} → p ⊕ q ⊕ r ⇓ v → p ⊕ (q ⊕ r) ⇓ v
-- conv-plus-assoc (conv-l (conv-l c _) _) = conv-l c _
-- conv-plus-assoc (conv-l (conv-r _ c) _) = conv-r _ (conv-l c _)
-- conv-plus-assoc (conv-r p c) =  conv-r _ (conv-r _ c)

-- conv-plus-assoc' : ∀  {A} {p q r : ND A} {v : A} → p ⊕ (q ⊕ r) ⇓ v → p ⊕ q ⊕ r ⇓ v
-- conv-plus-assoc' (conv-l c _ ) = conv-l (conv-l c _) _
-- conv-plus-assoc' (conv-r _ (conv-l c _)) = conv-l (conv-r _ c) _
-- conv-plus-assoc' (conv-r _ (conv-r _ c)) = conv-r _ c


-- conv-plus-idem : ∀  {A} {v : A} {p : ND A} → p ⊕ p ⇓ v → p ⇓ v
-- conv-plus-idem (conv-l c _) =  c
-- conv-plus-idem (conv-r _ c) = c

-- conv-plus-idem' : ∀  {A} {v : A} {p : ND A} → p ⇓ v → p ⊕ p ⇓ v
-- conv-plus-idem' c = conv-l c _



-- conv-plus-comm : ∀  {A} {v : A} {p q : ND A} → p ⊕ q ⇓ v → q ⊕ p ⇓ v
-- conv-plus-comm (conv-l c _) = conv-r _ c
-- conv-plus-comm (conv-r _ c) = conv-l c _


-- --------------------------
-- -- non-determinism laws --
-- --------------------------

-- plus-unit-l : ∀  {A} {p : ND A} → zero ⊕ p ~ p
-- plus-unit-l = mk~ conv-plus-unit-l ( λ c → conv-r _ c)


-- plus-unit-r : ∀  {A} {p : ND A} → p ⊕ zero ~ p
-- plus-unit-r = mk~ conv-plus-unit-r ( λ c → conv-l c _)


-- plus-assoc : ∀  {A} {p q r : ND A} → (p ⊕ q) ⊕ r ~ p ⊕ (q ⊕ r)
-- plus-assoc = mk~ conv-plus-assoc conv-plus-assoc'


-- plus-idem : ∀  {A} (p : ND A) → p ⊕ p ~ p
-- plus-idem p = mk~ conv-plus-idem conv-plus-idem'


-- plus-comm : ∀  {A} {p q : ND A} → p ⊕ q ~ q ⊕ p
-- plus-comm = mk~ conv-plus-comm conv-plus-comm


-- plus-distr : ∀  {A B} {p q : ND A} {f : A → ND B}  → ((p ⊕ q) >>= f) ~ (p >>= f) ⊕ (q >>= f)
-- plus-distr = ~refl

-- zero-bind : ∀  {A B} {f : A → ND B} → (zero >>= f) ~ zero
-- zero-bind = ~refl

-- plus-distr-dup : ∀  {A B} {p : ND A} {q : ND B} {f : A → ND B}
--   → (p >>= f) ⊕ q ~ (p >>= λ x → f x ⊕ q) ⊕ q
-- plus-distr-dup  {p = ret x} {q} {f} =
--   f x ⊕ q
--   ~⟨ plus-cong-r (~symm (plus-idem q)) ⟩
--   f x ⊕ (q ⊕ q)
--   ~⟨  ~symm plus-assoc ⟩
--   f x ⊕ q ⊕ q
--   ∎
-- plus-distr-dup {p = zero} =  ~refl
-- plus-distr-dup {p = p1 ⊕ p2} {q} {f} = 
--   (p1 >>= f) ⊕ (p2 >>= f) ⊕ q
--   ~⟨ plus-assoc ⟩
--   (p1 >>= f) ⊕ ((p2 >>= f) ⊕ q)
--   ~⟨ plus-cong-r  (plus-distr-dup {p = p2}) ⟩
--   (p1 >>= f) ⊕ ((p2 >>= (λ x → f x ⊕ q)) ⊕ q)
--   ~⟨  plus-cong-r plus-comm ⟩
--   (p1 >>= f) ⊕ (q ⊕ (p2 >>= (λ x → f x ⊕ q)))
--   ~⟨  ~symm plus-assoc ⟩
--   (p1 >>= f) ⊕ q ⊕ (p2 >>= (λ x → f x ⊕ q))
--   ~⟨ plus-cong-l (plus-distr-dup {p = p1}) ⟩
--   ((p1 >>= (λ x → f x ⊕ q)) ⊕ q) ⊕ (p2 >>= (λ x → f x ⊕ q))
--   ~⟨ plus-cong-l plus-comm ⟩
--   (q ⊕ (p1 >>= (λ x → f x ⊕ q))) ⊕ (p2 >>= (λ x → f x ⊕ q))
--   ~⟨ plus-assoc ⟩
--   q ⊕ ((p1 >>= (λ x → f x ⊕ q)) ⊕ (p2 >>= (λ x → f x ⊕ q)))
--   ~⟨  plus-comm ⟩
--   (p1 >>= (λ x → f x ⊕ q)) ⊕ (p2 >>= (λ x → f x ⊕ q)) ⊕ q
--   ∎

-- interchange : ∀  {A B} {p : ND A} {q : ND B} {f : A → ND B} → (∃[ v ] p ⇓ v)
--   → (p >>= f) ⊕ q ~ (p >>= λ x → f x ⊕ q)
-- interchange {p = ret x} _ =  ~refl
-- interchange {p = zero} (v , ())
-- interchange {p = p1 ⊕ p2} {q} {f} (v , conv-l c .p2) =
--   ((p1 >>= f) ⊕ (p2 >>= f) ⊕ q)
--   ~⟨ plus-assoc ⟩
--   ((p1 >>= f) ⊕ ((p2 >>= f) ⊕ q))
--   ~⟨ plus-cong-r (plus-distr-dup {p = p2}) ⟩
--   ((p1 >>= f) ⊕ ((p2 >>= λ x → f x ⊕ q) ⊕ q))
--   ~⟨ plus-cong-r plus-comm ⟩
--   ((p1 >>= f) ⊕ (q ⊕ (p2 >>= λ x → f x ⊕ q)))
--   ~⟨ ~symm plus-assoc ⟩
--   ((p1 >>= f) ⊕ q ⊕ (p2 >>= λ x → f x ⊕ q))
--   ~⟨ plus-cong-l (interchange ( v , c)) ⟩
--   (p1 ⊕ p2 >>= (λ x → f x ⊕ q))
--   ∎
-- interchange {p = p1 ⊕ p2} {q} {f} (v , conv-r .p1 c) = 
--   ((p1 >>= f) ⊕ (p2 >>= f) ⊕ q)
--   ~⟨ plus-cong-l plus-comm ⟩
--   ((p2 >>= f) ⊕ (p1 >>= f) ⊕ q)
--   ~⟨ plus-assoc ⟩
--   ((p2 >>= f) ⊕ ((p1 >>= f) ⊕ q))
--   ~⟨ plus-cong-r (plus-distr-dup {p = p1}) ⟩
--   ((p2 >>= f) ⊕ ((p1 >>= λ x → f x ⊕ q) ⊕ q))
--   ~⟨ plus-cong-r plus-comm ⟩
--   ((p2 >>= f) ⊕ (q ⊕ (p1 >>= λ x → f x ⊕ q)))
--   ~⟨ ~symm plus-assoc ⟩
--   ((p2 >>= f) ⊕ q ⊕ (p1 >>= λ x → f x ⊕ q))
--   ~⟨  plus-cong-l (interchange (v , c)) ⟩
--   ((p2 >>= λ x → f x ⊕ q) ⊕ (p1 >>= λ x → f x ⊕ q))
--   ~⟨ plus-comm ⟩
--   (p1 ⊕ p2 >>= (λ x → f x ⊕ q))
--   ∎



-- -- Pattern matching


-- match : ∀ {A B C : Set} → (A → Maybe B) → ND C → (B → ND C) → A → ND C
-- match m d f a with m a
-- ... | just x =  f x
-- ... | nothing = d

-- getJust : ∀ {A B : Set} → ND B → (A → ND B) → Maybe A → ND B
-- getJust = match id


-- match-assoc : ∀{A B C D} (c : A → Maybe B) (m : ND A) {d : ND C}
--                {f : B → ND C}{g : C → ND D} →
--                ((m >>= match c d f) >>= g) ~ (m >>= match c (d >>= g) (λ x → f x >>=  g))
-- match-assoc {A} {B} c m {d} {f} {g} =
--   ~trans (bind-assoc m) ( bind-cong-r m (λ x → cases c x ))
--   where 
--   cases : (c : A → Maybe B) (x : A) →
--           (match c d f x >>= g) ~ (match c (d >>= g) (λ y → f y >>= g) x)
--   cases c x with c x
--   ... | just y  =  ~refl
--   ... | nothing =  ~refl

-- getJust-assoc : ∀{B C D} (m : ND (Maybe B)) {d : ND C}
--                {f : B → ND C}{g : C → ND D} →
--                ((m >>= getJust d f) >>= g) ~ (m >>= getJust (d >>= g) (λ x → f x >>= g))
-- getJust-assoc = match-assoc id


-- match-cong-default : ∀{A B C} (c : A → Maybe B) (m : ND A)
--   {d : ND C} {e : ND C} {f : B → ND C}
--                (h : d ~ e) →
--                (m >>= match c d f) ~ (m >>= match c e f)
-- match-cong-default {A} c m {d} {e} {f} h =  bind-cong-r m   cases
--   where cases : (a : A) → (match c d f a) ~ (match c e f a)
--         cases a with c a
--         ...| just x =  ~refl
--         ...| nothing = h


-- getJust-cong-default : ∀{B C} (m : ND (Maybe B))
--   {d : ND C} {e : ND C} {f : B → ND C}
--                (h : d ~ e) →
--                (m >>= getJust d f) ~ (m >>= getJust e f)
-- getJust-cong-default = match-cong-default id


-- match-cong : ∀{A B C} (c : A → Maybe B) (m : ND A) {d : ND C}
--                {f : B → ND C} {g : B → ND C}
--                (h : ∀ x → f x ~ g x) →
--                (m >>= match c d f) ~ (m >>= match c d g)
-- match-cong {A} c m {d} {f} {g} e =  bind-cong-r m  cases
--   where cases : (x : A) → match c d f x ~ match c d g x
--         cases x with c x
--         ...| just y =  e y
--         ...| nothing =  ~refl

-- getJust-cong : ∀{B C} (m : ND (Maybe B)) {d : ND C}
--                {f : B → ND C} {g : B → ND C}
--                (h : ∀ x → f x ~ g x) →
--                (m >>= getJust d f) ~ (m >>= getJust d g)
-- getJust-cong = match-cong id

-- match-distr :  ∀{A B C} (c : A → Maybe B)
--             {p q : ND C} {f : B → ND C} a
--             → match c p f a ⊕ q ~ match c (p ⊕ q) (λ x → f x ⊕ q) a
-- match-distr c a with c a
-- ... | nothing = ~refl
-- ... | just x = ~refl


-- match-interchange :  ∀{A B C} (c : A → Maybe B) {m : ND A}
--             {p q : ND C} {f : B → ND C} → ∃[ v ] m ⇓ v
--             → (m >>= λ a → match c p f a) ⊕ q ~ (m >>= λ a → match c (p ⊕ q) (λ x → f x ⊕ q) a)
-- match-interchange c {m} d = ~trans (interchange d) (bind-cong-r m ( λ a → match-distr c a))


-- getJust-interchange :  ∀{B C} {m : ND (Maybe B)}
--             {p q : ND C} {f : B → ND C} → ∃[ v ] m ⇓ v
--             → (m >>= λ a → getJust p f a) ⊕ q ~ (m >>= λ a → getJust (p ⊕ q) (λ x → f x ⊕ q) a)
-- getJust-interchange = match-interchange id


-- -- reasoning about convergence

-- pos-ret : ∀ {A} {x : A} → ∃[ v ] ret x ⇓ v
-- pos-ret {x = x} = x , conv-ret x
-- pos-plus-l : ∀ {A} {p q : ND A} → ∃[ v ] p ⇓ v → ∃[ v ] p ⊕ q ⇓ v
-- pos-plus-l (v , c) = v , conv-l c _
-- pos-bind : ∀ {A B} (p : ND A) {f : A → ND B} → ∃[ v ] p ⇓ v → (∀ w → ∃[ v ] f w ⇓ v) → ∃[ v ] (p >>= f) ⇓ v
-- pos-bind p (v , c) f with f v
-- ...| w , d =  w , bind-cong-conv  c d

-- pos-getJust : ∀ {A B} (p : ND B) {f : A → ND B} (m : Maybe A) → ∃[ v ] p ⇓ v → (∀ w → ∃[ v ] f w ⇓ v) → ∃[ v ] (getJust p f m) ⇓ v
-- pos-getJust p nothing c f = c
-- pos-getJust p (just x) c f = f x
             