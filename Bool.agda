module Bool where

open import Agda.Primitive
open import Binary.Associative

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

and : 𝔹 → 𝔹 → 𝔹
and true true = true
and _ _ = false

or : 𝔹 → 𝔹 → 𝔹
or false false = false
or _ _ = true

if_then_else : {A : Set} → 𝔹 → A → A → A
if_then_else true a _ = a
if_then_else false _ b = b

not : 𝔹 → 𝔹
not true = false
not false = true


