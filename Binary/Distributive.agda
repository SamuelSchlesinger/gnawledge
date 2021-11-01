module Binary.Distributive where

open import Agda.Primitive
open import Equality

Distributive : {l : Level} (A : Set l) -> (mulOp addOp : A -> A -> A) -> Set l
Distributive A mulOp addOp = (a b c : A) -> mulOp a (addOp b c) ≡ addOp (mulOp a b) (mulOp a c)
