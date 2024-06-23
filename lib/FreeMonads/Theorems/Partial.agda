{-# OPTIONS --unicode --guardedness #-}
module FreeMonads.Theorems.Partial where

open import FreeMonads.Structure.Effect
open import FreeMonads.Structure.Free
open import FreeMonads.Partial
open import Function
open import Axiom.Extensionality.Propositional
open import Function
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Data.Bool
open import Data.Product
open import Data.Unit
open import Data.Nat
open import Level using (Level)

-- Include functional extensionality
private
  variable
    level : Level

postulate
  -- functional extensionality: if equal inputs produce equal outputs then the functions are equal
  funext : Extensionality level level

Partial = PartialFree

infix 3 _~_
-- infix 6 _~[_]_

---------------------------
-- (strong) bisimilarity --
---------------------------

-- Note from the original proof: We define strong bisimilarity in the style of Danielsson. We prove
-- later that this definition is equivalent to the definition in the
-- paper (see theorem `equiv-iconv~`).
data _~_ {A : Set} : (a? b? : Partial A) → Set where
  ~now   : ∀ a → now a ~ now a
  ~later : ∀ {a b later-a later-b} (eq : a ~ b) → (later-a ≡ later a) → (later-b ≡ later b) → later-a ~ later-b


Unit-eta : ∀ {A : Set} (f : ⊤ → A) → f ≡ λ _ → f tt
Unit-eta f = funext λ {tt → refl }

Unit-eta' : ∀ {A : Set} {f g : ⊤ → A} → f ≡ g → f tt ≡ g tt
Unit-eta' {f = f} {g = g} refl = refl

later-extraction : ∀ {A} (cont : Effect.Ret PartialEffect LaterOp → Free PartialEffect A)
  → ∃ λ a → later a ≡ impure (LaterOp , cont)
later-extraction cont = (cont tt , (impure-inj' (sym (Unit-eta cont))))

later-inj : ∀ {A} {a b : Partial A} → later a ≡ later b → a ≡ b
later-inj {a = a} {b = b} eq with impure-inj eq
... | r with (Unit-eta' r)
... | refl = refl

~later-op : ∀ {A} {a b : Partial A}
  → later a ~ b
  → ∃ λ b' → b ≡ later b'
~later-op (~later {b = b'} {later-b = b} conv-ab eq-a eq-b ) with later-inj eq-a
... | refl = b' , eq-b

-- Reflexivity

-- TODO: Determine if terminating
{-# TERMINATING #-}
~refl  : ∀ {A} (a? : Partial A) → _~_ a? a?
~refl (pure a) = ~now a
~refl (impure (LaterOp , k)) with later-extraction k
... | a , refl = ~later (~refl a) refl refl
-- ... | a , refl = ~later (~refl a)


-- Transitivity
~trans : ∀ {A} {a b c : Partial A}
  (eq : a ~ b) (eq' : b ~ c) → a ~ c
~trans (~now a) (~now .a) = ~now a
~trans (~later eq1 refl refl) (~later eq2 rlb refl) with later-inj rlb
... | refl = ~later (~trans eq1 eq2) refl refl

-- indexed bisimilarity

data _~[_]_ {A : Set} : (a : Partial A) → (i : ℕ) → (b : Partial A) → Set where
  ~izero   : ∀ {a b} → a ~[ 0 ] b
  ~inow   : ∀ i a → now a ~[ i ] now a
  ~ilater : ∀ {i a b la lb} (eq : a ~[ i ] b) → (la ≡ later a) → (lb ≡ later b) → la ~[ suc i ] lb

-- indexed bisimilarity implies bisimilairity


-- TODO: Determine if terminating
{-# TERMINATING #-}
stepped : ∀ {A} (a b : Partial A) → (∀ i → a ~[ i ] b) → _~_ a b
stepped (pure x) (pure y) eq with eq 1
... | ~inow _ _  =  ~now x
stepped (pure x) (impure (LaterOp , cont)) eq with eq 1
... | ~ilater e () rb
stepped (impure x) (pure y) eq with eq 1
... | ~ilater e ra ()
stepped (impure (LaterOp , contx)) (impure (LaterOp , conty)) eq with later-extraction contx | later-extraction conty
... | x , refl | y , refl = ~later (stepped x y (λ i -> stepped-later i x y (eq (suc i)))) refl refl
  where stepped-later : ∀ {A} i (a b : Partial A) →
                        (later a  ~[ suc i ] later b) →  a ~[ i ] b
        stepped-later i a b (~ilater e r-la r-lb) with later-inj r-la | later-inj r-lb
        ... | refl | refl = e


-- reflexivity

~irefl'  : ∀ {i A} (a : Partial A) → a ~[ i ] a
~irefl' {zero} a =  ~izero
~irefl' {suc i} (pure x) = ~inow (suc i) x
~irefl' {suc i} (impure (LaterOp , cont)) with later-extraction cont
... | x , refl = ~ilater (~irefl' x) refl refl

~irefl  : ∀ {i A} {a : Partial A} → a ~[ i ] a
~irefl {_} {_} {a} =  ~irefl' a


-- Transitivity


~itrans : ∀ {i A} {a b c : Partial A}
  (eq : a ~[ i ] b) (eq' : b ~[ i ] c) → a ~[ i ] c
~itrans {zero} eq eq' = ~izero
~itrans {suc i} (~inow .(suc i) a) (~inow .(suc i) .a) = ~inow (suc i) a
~itrans {suc i} (~ilater eq refl refl) (~ilater eq' r1 refl) with later-inj r1
... | refl = ~ilater (~itrans eq eq') refl refl


-- Symmetry


~isymm : ∀ {i A} {a b : Partial A}
  (eq : a ~[ i ] b) → b ~[ i ] a
~isymm {zero} eq  = ~izero
~isymm (~inow i a) =  ~inow i a
~isymm {suc i} (~ilater eq refl refl) = ~ilater (~isymm eq) refl refl


_~⟨_⟩_ : ∀ {A : Set} {i} (x : Partial A) → ∀ {y : Partial A} {z : Partial A} → x ~[ i ] y → y ~[ i ] z → x ~[ i ] z
_~⟨_⟩_ {_} x r eq =  ~itrans r eq


_~⟨⟩_ : ∀ {A : Set} {i} (x : Partial A) → ∀ {y : Partial A} → x ~[ i ] y → x ~[ i ] y
_~⟨⟩_  x eq = eq



_∎ : ∀ {A : Set} {i} (x : Partial A) → x ~[ i ] x
_∎  x = ~irefl

infix  3 _∎
infixr 1 _~⟨_⟩_
infixr 1 _~⟨⟩_

~idown : ∀ {i} {A} {a b : Partial A} -> a ~[ suc i ] b -> a ~[ i ] b
~idown {i} (~inow .(suc _) a) = ~inow i a
~idown {zero} (~ilater eq refl refl) = ~izero
~idown {suc i} (~ilater eq refl refl) = ~ilater ( ~idown eq) refl refl


bind-cong : ∀ {i A B}  {a b : Partial A} (eq : a ~[ i ] b)
            {k l : A → Partial B} (h : ∀ a → (k a) ~[ i ] (l a)) →
            (a >>= k) ~[ i ] (b >>= l)
bind-cong (~izero) g = ~izero
bind-cong (~inow _ a) g =  g a
bind-cong {suc i} (~ilater h refl refl) g =  ~ilater ( bind-cong h \ a' -> ~idown (g a')) refl refl


bind-cong-l : ∀ {i A B}  {a b : Partial A} (eq : a ~[ i ] b)
            {k : A → Partial B} →
            (a >>= k) ~[ i ] (b >>= k)
bind-cong-l (~izero) = ~izero
bind-cong-l (~inow a _) =  ~irefl
bind-cong-l (~ilater eq refl refl) = ~ilater ( bind-cong-l eq) refl refl


bind-cong-r : ∀ {i A B}  (a : Partial A)
            {k l : A → Partial B} (h : ∀ a → (k a) ~[ i ] (l a)) →
            (a >>= k) ~[ i ] (a >>= l)
bind-cong-r (pure x) eq = eq x
bind-cong-r {zero} (impure (LaterOp , cont)) eq with later-extraction cont
... | x , refl =  ~izero
bind-cong-r {suc i} (impure (LaterOp , cont)) eq with later-extraction cont
... | x , refl = ~ilater (bind-cong-r x \ a' -> ~idown (eq a') ) refl refl


bind-assoc : ∀{i A B C}(m : Partial A)
                 {k : A → Partial B}{l : B → Partial C} →
                 ((m >>= k) >>= l) ~[ i ] (m >>= λ a → k a >>= l)
bind-assoc (pure x) =  ~irefl
bind-assoc {zero} (impure (LaterOp , cont)) with later-extraction cont
... | x , refl = ~izero
bind-assoc {suc i} (impure (LaterOp , cont)) with later-extraction cont
... | x , refl = ~ilater ( bind-assoc (x)) refl refl


-- original definition:
-- mutual
--   never : ∀ {a i} -> Partial a i
--   never = later ∞never

--   ∞never : ∀ {a i} -> ∞Partial a i
--   force ∞never = never

-- TODO: Find a way to express this correctly
-- Because this is definetively not terminating 😅
-- never : ∀ {a} -> Partial a
-- never = impure (LaterOp , λ _ -> never)

{-

-- 
-- Starting here the theorems rely on never, which is non-terminating, so the proof checker _will_ get stuck.
--

if-bind : ∀ {A B n} {x y : Partial A} {f : A → Partial B} b 
  → ((if b then x else y) >>= f) ~[ n ] (if b then (x >>= f) else (y >>= f))
if-bind false =  ~irefl
if-bind true = ~irefl


if-then-cong : ∀ b {A n} {x y x' : Partial A} (eq : x ~[ n ] x') → (if b then x else y) ~[ n ] (if b then x' else y)
if-then-cong false eq = ~irefl
if-then-cong true eq =  eq

never-bind : ∀ {i A B} {f : A → Partial B} → (never >>= f) ~[ i ] never
never-bind {0} = ~izero
never-bind {suc i} =  ~ilater never-bind refl refl

bind-never : ∀ {i A B} (m : Partial A) → _~[_]_ {B} (m >>= (λ x → never)) i never
bind-never {zero} m = ~izero
bind-never {suc i} (now x) = ~irefl
bind-never {suc i} (later x) =  ~ilater ( bind-never (force x))




match : ∀ {i} {A B C : Set} → (A → Maybe B) → Partial C i → (B → Partial C i) → A → Partial C i
match m d f a with m a
... | just x =  f x
... | nothing = d

getJust : ∀ {i} {A B : Set} → Partial B i → (A → Partial B i) → Maybe A → Partial B i
getJust = match id




match-assoc : ∀{i A B C D} (c : A → Maybe B) (m : Partial A) {d : Partial C ∞}
               {f : B → Partial C ∞}{g : C → Partial D ∞} →
               ((m >>= match c d f) >>= g) ~[ i ] (m >>= match c (d >>= g) (λ x → f x >>=  g))
match-assoc {i} {A} {B} c m {d} {f} {g} =
  ~itrans (bind-assoc m) ( bind-cong-r m (λ x → cases c x ))
  where 
  cases : (c : A → Maybe B) (x : A) →
          (match c d f x >>= g) ~[ i ] (match c (d >>= g) (λ y → f y >>= g) x)
  cases c x with c x
  ... | just y  =  ~irefl
  ... | nothing =  ~irefl


match-cong-default : ∀{i A B C} (c : A → Maybe B) (m : Partial A)
  {d : Partial C ∞} {e : Partial C ∞} {f : B → Partial C ∞}
               (h : d ~[ i ] e) →
               (m >>= match c d f) ~[ i ] (m >>= match c e f)
match-cong-default {i} {A} c m {d} {e} {f} h =  bind-cong-r m   cases
  where cases : (a : A) → (match c d f a) ~[ i ] (match c e f a)
        cases a with c a
        ...| just x =  ~irefl
        ...| nothing = h

match-cong : ∀{i A B C} (c : A → Maybe B) (m : Partial A) {d : Partial C ∞}
               {f : B → Partial C ∞} {g : B → Partial C ∞}
               (h : ∀ x → f x ~[ i ] g x) →
               (m >>= match c d f) ~[ i ] (m >>= match c d g)
match-cong {i} {A} c m {d} {f} {g} e =  bind-cong-r m  cases
  where cases : (x : A) → match c d f x ~[ i ] match c d g x
        cases x with c x
        ...| just y =  e y
        ...| nothing =  ~irefl


-- Prove that the indexed bisimilarity relation can be characterised
-- using the indexed convergence relation (defined below) as follows:
--
--   p ~[i] q  <=> (∀ j < i, v. p ⇓[j] v <=> q ⇓[j] v)
--

data _⇓[_]_ {A : Set} : Partial A → ℕ → A → Set where
  iconv-now : ∀{i} → (x : A) → now x ⇓[ i ] x
  iconv-later :  ∀{i} → {v : A} → {p : ∞Partial A} → force p ⇓[ i ] v → (later p) ⇓[ suc i ] v

-- lemmas 
~iconv : ∀ {A} {i} {j} {p : Partial A} {q : Partial A} {v} →  (le : j < i) → p ~[ i ] q → p ⇓[ j ] v → q ⇓[ j ] v
~iconv l (~inow _ a) c = c
~iconv (s≤s (s≤s l)) (~ilater e) (iconv-later c) = iconv-later (~iconv (s≤s l) e c)


conv-inv : ∀ {A} {p : Partial A} {v : A} → p ⇓[ 0 ] v → p ≡ now v
conv-inv (iconv-now _) = refl

conv-inv' : ∀ {B : Set} {A : Set} {p : ∞Partial A} {v : A} → (later p) ⇓[ 0 ] v → B
conv-inv' ()

conv-down : ∀ {i} {A} {x} {y} → (∀ {j} {v : A} → j < suc i → (later x) ⇓[ j ] v → (later y) ⇓[ j ] v)
  → ({j : ℕ} {v : A} → j < i → force x ⇓[ j ] v → force y ⇓[ j ] v)
conv-down f le c with f (s≤s le) (iconv-later c)
... | iconv-later d = d


iconv~ : ∀ {A} {i} {p : Partial A} {q : Partial A}
  → (∀ {j}{v} →  (le : j < i) → p ⇓[ j ] v → q ⇓[ j ] v)
  → (∀ {j}{v} →  (le : j < i) → q ⇓[ j ] v → p ⇓[ j ] v)
  → p ~[ i ] q
iconv~ {i = zero} f g = ~izero
iconv~ {i = suc i} {now x} f g with conv-inv (f (s≤s z≤n) (iconv-now x))
... | refl = ~inow (suc i) x
iconv~ {i = suc i} {later x} { now y} f g = conv-inv' (g (s≤s z≤n) (iconv-now y))
iconv~ {i = suc i} {later x} {later y} f g = ~ilater (iconv~ ( conv-down f) ( conv-down g))

-- Theorem: p ~[i] q  <=> (∀ j < i, v. p ⇓[j] v <=> q ⇓[j] v)

equiv-iconv~ : ∀ {A} {i} {p : Partial A} {q : Partial A}
  →  p ~[ i ] q ⇔ (∀ {j}{v} → (le : j < i) → p ⇓[ j ] v ⇔  q ⇓[ j ] v)
equiv-iconv~ {A} {i} {p} {q} = mk⇔  to  from
  where from : ({j : ℕ} {v : A} → j < i → (p ⇓[ j ] v) ⇔ (q ⇓[ j ] v)) →
            p ~[ i ] q
        from eq = iconv~ ( λ le c → Equivalence.f (eq le) c)  ( λ le c → Equivalence.g (eq le) c)
        to : p ~[ i ] q → {j : ℕ} {v : A} → j < i → (p ⇓[ j ] v) ⇔ (q ⇓[ j ] v)
        to eq le = mk⇔ (~iconv le eq) (~iconv le (~isymm eq))


-- Prove that the indexed bisimilarity relation can be characterised
-- using the indexed convergence relation and the indexed divergence
-- relation (defined below) as follows:
--
--   p ~[i] q  <=> (∀ j < i, v. p ⇓[j] v => q ⇓[j] v) ∧ (∀ j ≤ i. p ⇑[j] => q ⇑[j])
--

data _⇑[_] {A : Set} : Partial A → ℕ → Set where
  idiv-zero : ∀ (p : Partial A) → p ⇑[ 0 ]
  idiv-suc :  ∀{i} → {p : ∞Partial A} → force p ⇑[ i ] → (later p) ⇑[ suc i ]

~idiv : ∀ {A} {i} {j} {p : Partial A} {q : Partial A} → (le : j ≤ i) →  p ~[ i ] q → p ⇑[ j ] → q ⇑[ j ]
~idiv z≤n ~izero d = idiv-zero _
~idiv le (~inow _ a) d = d
~idiv z≤n (~ilater e) d = idiv-zero _
~idiv (s≤s le) (~ilater e) (idiv-suc d) = idiv-suc (~idiv le e d)

idiv~ : ∀ {A} {i} {p : Partial A} {q : Partial A}
  → (∀ {j}{v} →  (le : j < i) → p ⇓[ j ] v → q ⇓[ j ] v)
  → (∀ {j} →  (le : j ≤ i) →  p ⇑[ j ] → q ⇑[ j ])
  → p ~[ i ] q
idiv~ {i = zero} c d = ~izero
idiv~ {i = suc i} {now x} c d  with conv-inv (c (s≤s z≤n) (iconv-now x))
... | refl = ~inow (suc i) x
idiv~ {A} {suc i} {later x} c d with d ( s≤s z≤n) (idiv-suc (idiv-zero _))
...| idiv-suc {p = p} (idiv-zero .(force p)) = ~ilater (idiv~ (conv-down c) ( down d))
  where down : ({j : ℕ} → j ≤ suc i → (later x) ⇑[ j ] → (later p) ⇑[ j ])
               → {j : ℕ} → j ≤ i → force x ⇑[ j ] → force p ⇑[ j ]
        down h l d with h (s≤s l) (idiv-suc d)
        ... | idiv-suc r = r

-- Theorem: p ~[i] q  <=> (∀ j < i, v. p ⇓[j] v => q ⇓[j] v) ∧ (∀ j ≤ i. p ⇑[j] => q ⇑[j])

equiv-idiv~ : ∀ {A} {i} {p : Partial A} {q : Partial A}
  → p ~[ i ] q ⇔ ((∀ {j}{v} → (j < i) → p ⇓[ j ] v →  q ⇓[ j ] v) ×
                  (∀ {j} → (j ≤ i) → p ⇑[ j ] → q ⇑[ j ]))
equiv-idiv~ {A} {i} {p} {q} =  mk⇔  to
                                    (λ (c , d) → idiv~ c  d)
  where to : p ~[ i ] q → ({j : ℕ} {v : A} → j < i → p ⇓[ j ] v → q ⇓[ j ] v)
                        × ({j : ℕ} → j ≤ i → p ⇑[ j ] → q ⇑[ j ])
        to eq =  ( λ le c → ~iconv le eq c) ,  λ le d → ~idiv le eq d
-}     