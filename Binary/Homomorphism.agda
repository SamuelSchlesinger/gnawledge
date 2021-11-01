module Binary.Homomorphism where

open import Equality
open import Agda.Primitive

Homomorphism :
  {l l' : Level}
  (A : Set l)
  (op : A -> A -> A)
  (B : Set l')
  (op' : B -> B -> B)
  (f : A -> B)
  -> Set (l ⊔ l')
Homomorphism A op B op' f = (a b : A) -> f (op a b) ≡ op' (f a) (f b)
