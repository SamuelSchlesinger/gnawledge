module Binary.Commutative where

open import Equality
open import Agda.Primitive

Commutative : { l : Level } (A : Set l) (op : A -> A -> A) -> Set l
Commutative A op = (a b : A) -> op a b ≡ op b a
