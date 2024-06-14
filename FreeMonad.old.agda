
-- data Partial (A : Set) : Set where
--   Now : A → Partial A
--   Later : Partial A -> Partial A

data PartialOp : Set where
  later : PartialOp

open PartialOp

PartialRet : PartialOp → Set
PartialRet later = PartialOp

PartialEffect : Effect
PartialEffect = PartialOp ▷ PartialRet

PartialFree = Free PartialEffect

nowF : ∀ {A} → A → PartialFree A
nowF A = pure A

example1 : PartialFree ℕ
example1 = nowF 42

laterF : ∀ {A} → PartialFree A → PartialFree A
laterF pa = impure (later , λ _ → pa)

example : PartialFree ℕ
example = laterF (nowF 42)



-- PartialMonad : RawMonad

-- data FreeF (F : Container → Set → Set) (Sig : Container) (A : Set) : Set where
--   pure : A -> FreeF F Sig A
--   impure : ⟦ Sig ⟧ F Sig A -> FreeF F Sig A

-- data PartialF (A : Set) : Set where
--   Later : PartialF A -> PartialF A

-- data PartialShape : Set where
--   later : PartialShape


-- PartialPosition : PartialShape -> Set
-- PartialPosition later = ⊤  -- There is only one position for `later`

-- PartialSig : Container
-- PartialSig = record
--   { Shape = PartialShape
--   ; Position = PartialPosition
--   }


-- partialFree : PartialF ⋆    