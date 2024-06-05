open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Category.Monad public

module WithPartial where
  
Type = Set

data Expr : Type where
  Val : Nat → Expr
  Add : Expr → Expr → Expr
  Loop : Expr

data Partial (A : Type) : Type where
  Now : A → Partial A
  Later : Partial A → Partial A

-- Partial-Monad : Monad Partial
-- Partial-Monad = makeMonad pure bind r1 r2 r3
--   where
--     pure : {A : Type} → A → Partial A
--     pure = Now
    
--     bind : ∀ {A B} → Partial A → (A → Partial B) → Partial B
--     bind (Now x) f = f x
--     bind (Later p) f = Later (bind p f)

--     r1 : ∀ {A B} → (x : A) → (f : A → Partial B) → bind (pure x) f ≡ f x
--     r1 = {!!}

--     r2 : ∀ {A} → (m : Partial A) → bind m pure ≡ m
--     r2 = {!!}

--     r3 : ∀ {A B C} → (m : Partial A) → (f : A → Partial B) → (g : B → Partial C) → bind (bind m f) g ≡ bind m (λ x → bind (f x) g)
--     r3 = {!!}

Partial-Monad : RawMonad Partial
Partial-Monad = makeRawMonad pure bind
  where
    pure : {A : Type} → A → Partial A
    pure = Now
    
    bind : ∀ {A B} → Partial A → (A → Partial B) → Partial B
    bind (Now x) f = f x
    bind (Later p) f = Later (bind p f)
  
eval : Expr → Partial Nat
eval (Val n) = Now n
eval (Add e1 e2) = do
  n1 ← eval e1
  n2 ← eval e2
  Now (n1 + n2)
eval Loop = Later (eval Loop)
