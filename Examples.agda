
open import Agda.Builtin.Nat

apply : (A : Set)(B : A -> Set) -> ((x : A) -> B x) -> (a : A) -> B a
apply A B f a = f a


record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A


from : Nat → Stream Nat
from n = record { head = n; tail = from (suc n) }