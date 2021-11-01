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

ComposeHomomorphisms : 
  {l l' l'' : Level}
  (A : Set l)
  (op : A -> A -> A)
  (B : Set l')
  (op' : B -> B -> B)
  (f : A -> B)
  (C : Set l'')
  (op'' : C -> C -> C)
  (f' : B -> C)
  -> Homomorphism A op B op' f
  -> Homomorphism B op' C op'' f'
  -> Homomorphism A op C op'' (\x -> f' (f x))
ComposeHomomorphisms A op B op' f C op'' f' hom hom' a a' =
     hom' (f a) (f a')
  ∙≡ cong f' (hom a a')
