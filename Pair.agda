module Pair where

open import Agda.Primitive
open import Equality

data _&_ {l l' : Level} : (A : Set l) -> (B : A -> Set l') -> Set (l ⊔ l') where
  pair : { A : Set l } { B : A -> Set l' } (a : A) (b : B a) -> A & B

fst : {l l' : Level} {A : Set l} {B : A → Set l'} → A & B → A
fst (pair a _) = a

snd : {l l' : Level} {A : Set l} {B : A → Set l'} → (p : A & B) → B (fst p)
snd (pair _ b) = b
