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


-- Functor instance for the container
-- instance
--   fmap : Functor {I = Shape} {Pos = Position}
--   fmap {A} {B} f = λ { (later , pos) -> (later , f pos) }

-- -- Define the partial functor using the container
-- partialF : Functor (Container.toFunctor PartialSig)
-- partialF = Container.toFunctor PartialSig

-- -- Example usage: defining a simple value
-- example : GuardedFix partialF
-- example = unfoldG (λ _ -> later , tt)

-- partialFree : PartialF ⋆