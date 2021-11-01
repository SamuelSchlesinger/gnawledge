module Binary.Cancellative where

open import Equality
open import Agda.Primitive

LeftCancellative : {l : Level} (A : Set l) → (op : A → A → A) → (c : A) → Set l
LeftCancellative A op c = (a : A) → op a c ≡ c

RightCancellative : {l : Level} (A : Set l) -> (op : A -> A -> A) -> (c : A) -> Set l
RightCancellative A op c = (a : A) → op c a ≡ c
