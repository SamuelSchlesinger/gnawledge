module Finite where

open import Naturals
open import Equality
open import Bool

data Fin : ℕ -> Set where
  finsuc : {n : ℕ} -> Fin n -> Fin (suc n)
  finzero : {n : ℕ} -> Fin (suc n)

_==Fin_ : {n : ℕ} → Fin n → Fin n → 𝔹
_==Fin_ finzero finzero = true
_==Fin_ (finsuc n) (finsuc m) = n ==Fin m
_==Fin_ _ _ = false
