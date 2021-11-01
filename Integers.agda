module Integers where

open import Agda.Primitive
open import Equality
open import Naturals

-- Ones comlement
data ℤ : Set where
  ℤ+ : ℕ → ℤ
  ℤ- : ℕ → ℤ
{-# BUILTIN INTEGER       ℤ  #-}
{-# BUILTIN INTEGERPOS    ℤ+ #-}
{-# BUILTIN INTEGERNEGSUC ℤ- #-}

-- TODO(sam) do classish stuff so that numbers work how I'd like
fromNegℤ : ℕ → ℤ
fromNegℤ 0 = ℤ+ 0
fromNegℤ (suc n) = ℤ+ n
{-# BUILTIN FROMNEG fromNegℤ #-}

