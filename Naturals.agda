module Naturals where

open import Agda.Primitive
open import Equality
open import Binary.Homomorphism
open import Binary.Commutative
open import Binary.Identity
open import Binary.Associative
open import Binary.Cancellative
open import Binary.Distributive

data ℕ : Set where
  suc : ℕ → ℕ
  zero : ℕ
{-# BUILTIN NATURAL ℕ #-}

_+ℕ_ : ℕ → ℕ → ℕ
_+ℕ_ zero m = m
_+ℕ_ (suc n) m = suc (_+ℕ_ n m)

infixr 4 _+ℕ_

_×ℕ_ : ℕ → ℕ → ℕ
_×ℕ_ zero m = zero
_×ℕ_ (suc n) m = m +ℕ (n ×ℕ m)

infixr 8 _×ℕ_

_^ℕ_ : ℕ → ℕ → ℕ
_^ℕ_ n zero = suc zero
_^ℕ_ n (suc m) = n ×ℕ n ^ℕ m

pf : 2 ^ℕ 4 ≡ 16
pf = refl

infixr 16 _^ℕ_

LeftIdentity+ℕ : LeftIdentity ℕ _+ℕ_ 0
LeftIdentity+ℕ _ = refl

RightIdentity+ℕ : RightIdentity ℕ _+ℕ_ 0
RightIdentity+ℕ zero = refl
RightIdentity+ℕ (suc n) = cong suc (RightIdentity+ℕ n)

Commutative+ℕ : Commutative ℕ _+ℕ_
Commutative+ℕ zero m = sym (RightIdentity+ℕ m)
Commutative+ℕ (suc n) m =
  lem m n ∙≡ cong suc (Commutative+ℕ n m)
  where
  lem : (a b : ℕ) -> suc a +ℕ b ≡ a +ℕ suc b
  lem zero b = refl
  lem (suc a) b = cong suc (lem a b)

Associative+ℕ : Associative ℕ _+ℕ_
Associative+ℕ zero b c = refl
Associative+ℕ (suc a) b c = cong suc (Associative+ℕ a b c)

LeftIdentity×ℕ : LeftIdentity ℕ _×ℕ_ 1
LeftIdentity×ℕ n = RightIdentity+ℕ n

RightIdentity×ℕ : RightIdentity ℕ _×ℕ_ 1
RightIdentity×ℕ zero = refl
RightIdentity×ℕ (suc n) = cong suc (RightIdentity×ℕ n)

LeftCancellative×ℕ : LeftCancellative ℕ _×ℕ_ 0
LeftCancellative×ℕ zero = refl
LeftCancellative×ℕ (suc n) = LeftCancellative×ℕ n

Commutative×ℕ : Commutative ℕ _×ℕ_
Commutative×ℕ zero m = sym (LeftCancellative×ℕ m)
Commutative×ℕ (suc n) m = lem m n ∙≡ cong (\x -> m +ℕ x) (sym (Commutative×ℕ m n))
  where
  lem : (n m : ℕ) -> n +ℕ n ×ℕ m ≡ n ×ℕ suc m 
  lem zero m = refl
  lem (suc n) m = cong suc
    (  cong (\x -> m +ℕ x) (lem n m)
    ∙≡ sym (Associative+ℕ m n (n ×ℕ m))
    ∙≡ cong (\x -> x +ℕ n ×ℕ m) (Commutative+ℕ n m)
    ∙≡ Associative+ℕ n m (n ×ℕ m)
    )

Distributive×+ℕ : Distributive ℕ _×ℕ_ _+ℕ_
Distributive×+ℕ zero b c = refl
Distributive×+ℕ (suc a) b c =
     Associative+ℕ b (a ×ℕ b) (c +ℕ a ×ℕ c)
  ∙≡ cong (\x -> b +ℕ x)
    ( sym (Associative+ℕ (a ×ℕ b) c (a ×ℕ c))
    ∙≡ cong (\x -> x +ℕ a ×ℕ c) (Commutative+ℕ c (a ×ℕ b))
    ∙≡ Associative+ℕ c (a ×ℕ b) (a ×ℕ c)
    )
  ∙≡ sym (Associative+ℕ b c (a ×ℕ b +ℕ a ×ℕ c))
  ∙≡ cong (\x -> (b +ℕ c) +ℕ x) (Distributive×+ℕ a b c)

Associative×ℕ : Associative ℕ _×ℕ_
Associative×ℕ zero b c = refl
Associative×ℕ (suc a) b c = ?

Homomorphism×+ℕ : (a : ℕ) -> Homomorphism ℕ _+ℕ_ ℕ _×ℕ_ (\x -> a ^ℕ x)
Homomorphism×+ℕ a zero c = sym (RightIdentity+ℕ (a ^ℕ c))
Homomorphism×+ℕ a (suc b) c =
  Associative×ℕ a (a ^ℕ b) (a ^ℕ c)
  ∙≡ cong (\x -> a ×ℕ x) (Homomorphism×+ℕ a b c)
