module Naturals where

open import Agda.Primitive
open import Equality
open import Pair
open import Bool
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

_==ℕ_ : ℕ → ℕ → 𝔹
_==ℕ_ zero zero = true
_==ℕ_ (suc n) (suc m) = n ==ℕ m
_==ℕ_ _ _ = false

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

infixr 16 _^ℕ_

LeftIdentity+ℕ : LeftIdentity ℕ _+ℕ_ 0
LeftIdentity+ℕ _ = refl

RightIdentity+ℕ : RightIdentity ℕ _+ℕ_ 0
RightIdentity+ℕ zero = refl
RightIdentity+ℕ (suc n) = cong suc (RightIdentity+ℕ n)

-- This is a rather useful, simple, and memorable
SuccessorSwapLemma : (a b : ℕ) → suc a +ℕ b ≡ a +ℕ suc b
SuccessorSwapLemma zero b = refl
SuccessorSwapLemma (suc a) b = cong suc (SuccessorSwapLemma a b)

Commutative+ℕ : Commutative ℕ _+ℕ_
Commutative+ℕ zero m = sym (RightIdentity+ℕ m)
Commutative+ℕ (suc n) m =
  SuccessorSwapLemma m n ∙≡ cong suc (Commutative+ℕ n m)

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
Associative×ℕ (suc a) b c =
     sym (Commutative×ℕ (b +ℕ a ×ℕ b) c)
  ∙≡ sym (Distributive×+ℕ c b (a ×ℕ b))
  ∙≡ cong (\x -> c ×ℕ b +ℕ x)
    (  sym (Associative×ℕ c a b)
    ∙≡ sym (cong (\x -> x ×ℕ b) (Commutative×ℕ c a))
    ∙≡ Associative×ℕ a c b
    ∙≡ sym (cong (\x -> a ×ℕ x) (Commutative×ℕ c b))
    ∙≡ sym (Associative×ℕ a b c)
    )
  ∙≡ cong (\x -> x +ℕ ((a ×ℕ b) ×ℕ c)) (Commutative×ℕ b c)
  ∙≡ cong (\x -> b ×ℕ c +ℕ x) (Associative×ℕ a b c)

Homomorphism×+ℕ : (a : ℕ) -> Homomorphism ℕ _+ℕ_ ℕ _×ℕ_ (\x -> a ^ℕ x)
Homomorphism×+ℕ a zero c = sym (RightIdentity+ℕ (a ^ℕ c))
Homomorphism×+ℕ a (suc b) c =
  Associative×ℕ a (a ^ℕ b) (a ^ℕ c)
  ∙≡ cong (\x -> a ×ℕ x) (Homomorphism×+ℕ a b c)

data _<ℕ_ : ℕ → ℕ → Set where
  ltℕ : { n m : ℕ } (d : ℕ) → n ≡ suc m +ℕ d → m <ℕ n

infixr 0 _<ℕ_

bottom<ℕ : (n : ℕ) → zero <ℕ suc n
bottom<ℕ n = ltℕ n refl

diffℕ : (n m : ℕ) → n <ℕ m → ℕ & \d → n +ℕ suc d ≡ m
diffℕ n m (ltℕ d refl) = pair d (sym (SuccessorSwapLemma n d))

trans<ℕ : (a b c : ℕ) → (b <ℕ c) → a <ℕ b → a <ℕ c
trans<ℕ a b c (ltℕ d refl) (ltℕ d' refl) = ltℕ (suc (d +ℕ d'))
  ( cong suc
    (  SuccessorSwapLemma a (d +ℕ d')
    ∙≡ cong suc
      (  cong (\x -> a +ℕ x) (Commutative+ℕ d' d)
      ∙≡ sym (Associative+ℕ a d' d)
      )
    )
  )

_∙<_ : {a b c : ℕ} → (b <ℕ c) → a <ℕ b → a <ℕ c
_∙<_ = trans<ℕ _ _ _

infixr 0 _∙<_

-- A proof of monotonicity is like a 'cong' for that particular function
Monotoneℕ : (f : ℕ → ℕ) → Set
Monotoneℕ f = (a b : ℕ) → a <ℕ b → f a <ℕ f b

Monotone+ℕ : (a : ℕ) → Monotoneℕ (\x -> a +ℕ x)
Monotone+ℕ a a' b' (ltℕ d refl) = ltℕ d
  (  cong suc (Associative+ℕ a a' d)
  ∙≡ sym (SuccessorSwapLemma a (a' +ℕ d))
  )

ComposeMonotoneℕ : (f : ℕ → ℕ) → Monotoneℕ f → (g : ℕ → ℕ) → Monotoneℕ g → Monotoneℕ (\x → f (g x))
ComposeMonotoneℕ f mf g mg a b (ltℕ d refl) = mf (g a) (g (suc (a +ℕ d))) (mg a (suc (a +ℕ d)) (lem a d))
  where
  lem : (a d : ℕ) → a <ℕ suc (a +ℕ d)
  lem zero d = bottom<ℕ d
  lem (suc a) d = Monotone+ℕ 1 a (suc a +ℕ d) (lem a d)

data Comparisonℕ (x y : ℕ) : Set where
  eq?ℕ : x ≡ y → Comparisonℕ x y
  lt?ℕ : x <ℕ y → Comparisonℕ x y
  gt?ℕ : y <ℕ x → Comparisonℕ x y 

compareℕ : (a b : ℕ) → Comparisonℕ a b
compareℕ zero zero = eq?ℕ refl
compareℕ (suc a) zero = gt?ℕ (bottom<ℕ a)
compareℕ zero (suc b) = lt?ℕ (bottom<ℕ b)
compareℕ (suc a) (suc b) = go (compareℕ a b)
  where
  go : Comparisonℕ a b → Comparisonℕ (suc a) (suc b)
  go (eq?ℕ refl) = eq?ℕ refl
  go (lt?ℕ (ltℕ d refl)) = lt?ℕ (ltℕ d refl)
  go (gt?ℕ (ltℕ d refl)) = gt?ℕ (ltℕ d refl)
