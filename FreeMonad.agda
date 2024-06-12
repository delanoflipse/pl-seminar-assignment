open import Data.Container.FreeMonad

data PartialF (A : Set) : Set where
  Later : PartialF A -> PartialF A

partialFree : PartialF ⋆