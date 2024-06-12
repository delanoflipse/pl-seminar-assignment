open import Data.Container.FreeMonad
open import Data.Container
open import Agda.Builtin.Unit
open import Agda.Primitive
-- open import Data.Container.Fixpoints.Guarded

data PartialF (A : Set) : Set where
  Later : PartialF A -> PartialF A

data PartialShape : Set where
  later : PartialShape


PartialPosition : PartialShape -> Set
PartialPosition later = ⊤  -- There is only one position for `later`

PartialSig : Container
PartialSig = record
  { Shape = PartialShape
  ; Position = PartialPosition
  }


-- partialFree : PartialF ⋆