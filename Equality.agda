module Equality where

open import Agda.Primitive

data _≡_ {l : Level} {A : Set l} : A -> A -> Set l where
  refl : {x : A} -> x ≡ x
{-# BUILTIN EQUALITY _≡_  #-}

infixr 0 _≡_

_∙≡_ : {l : Level} {A : Set l} {a b c : A} -> b ≡ c → a ≡ b → a ≡ c
_∙≡_ refl refl = refl

infixr 0 _∙≡_

sym : {l : Level} {A : Set l} {a b : A} -> a ≡ b -> b ≡ a
sym refl = refl

subst : {l l' : Level} {A : Set l} {C : A -> Set l'} {a b : A} -> a ≡ b -> C a -> C b
subst refl x = x

cong : {l l' : Level} {A : Set l} {B : Set l'} {a a' : A} (f : A -> B) -> a ≡ a' -> f a ≡ f a'
cong f refl = refl

id : {l : Level} {A : Set l} -> A -> A
id x = x

Leibniz : (l : Level) (A : Set l) -> A -> A -> Set (lsuc l)
Leibniz l A a b = {F : A -> Set l} -> F a -> F b

Leinbiz→≡ : (l : Level) (A : Set l) -> (a : A) -> (b : A) -> Leibniz l A a b -> a ≡ b
Leinbiz→≡ l A a b eq = eq {F} refl where
  F : A -> Set l
  F = _≡_ a

≡→Leibniz : (l : Level) (A : Set l) -> (a : A) -> (b : A) -> a ≡ b -> Leibniz l A a b
≡→Leibniz l A a b refl = id
