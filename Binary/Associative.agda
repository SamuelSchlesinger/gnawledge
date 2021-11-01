module Binary.Associative where

open import Agda.Primitive
open import Equality

Associative : {l : Level} (A : Set l) -> (op : A -> A -> A) -> Set l
Associative A op = (a b c : A) -> op a (op b c) ≡ op (op a b) c
