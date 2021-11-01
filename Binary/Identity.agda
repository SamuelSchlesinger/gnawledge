module Binary.Identity where

open import Equality
open import Agda.Primitive

LeftIdentity : {l : Level} (A : Set l) -> (op : A -> A -> A) -> (a : A) -> Set l
LeftIdentity A op a = (b : A) -> op a b ≡ b

RightIdentity : {l : Level} (A : Set l) -> (op : A -> A -> A) -> (a : A) -> Set l
RightIdentity A op a = (b : A) -> op b a ≡ b
