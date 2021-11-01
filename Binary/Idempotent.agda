module Binary.Idempotent where

open import Agda.Primitive
open import Equality

Idempotent : {l : Level} (A : Set l) (op : A -> A -> A) -> Set l
Idempotent A op = (a : A) → op a a ≡ a
