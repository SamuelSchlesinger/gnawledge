module Vectors where

open import Agda.Primitive
open import Equality
open import Naturals
open import Finite
open import Bool

data Vect {l : Level} : ℕ → Set l → Set l where
  _::_ : {A : Set l} {n : ℕ} → A → Vect n A → Vect (suc n) A
  empty : {A : Set l} → Vect 0 A

infixr 4 _::_

mapVect : {l l' : Level} {n : ℕ} {A : Set l} {B : Set l'} (f : A -> B) -> Vect n A -> Vect n B
mapVect f empty = empty
mapVect f (x :: xs) = f x :: mapVect f xs

foldrVect : {l l' : Level} {n : ℕ} {A : Set l} {B : Set l'} (f : A -> B -> B) -> Vect n A -> B -> B
foldrVect f empty = id
foldrVect f (x :: xs) b = f x (foldrVect f xs b)

eqVect : {l : Level} {n : ℕ} {A : Set l} → (A → A → 𝔹) → Vect n A → Vect n A → 𝔹
eqVect f empty empty = true
eqVect f (x :: xs) (y :: ys) = and (f x y) (eqVect f xs ys)

indexVect : {l : Level} {n : ℕ} {A : Set l} → Fin n → Vect n A → A
indexVect finzero (x :: xs) = x
indexVect (finsuc i) (_ :: xs) = indexVect i xs

indicesVect : (n : ℕ) → Vect n (Fin n)
indicesVect zero = empty
indicesVect (suc n) = finzero :: mapVect finsuc (indicesVect n)

MapFoldrTheoremVect : {l l' l'' : Level} {n : ℕ} {A : Set l} {B : Set l'} {X : Set l''} (f : A -> B -> B) -> (xs : Vect n X) -> (g : X -> A) -> (b : B) -> foldrVect f (mapVect g xs) b ≡ foldrVect (\a c -> f (g a) c) xs b
MapFoldrTheoremVect f empty g b = refl
MapFoldrTheoremVect f (x :: xs) g b = cong (f (g x)) (MapFoldrTheoremVect f xs g b)


