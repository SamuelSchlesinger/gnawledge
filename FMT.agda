module FMT where

open import Equality
open import Vectors
open import Naturals
open import Finite
open import Pair
open import Bool

-- Based on Immerman's definitions in Descriptive Complexity Theory
record Vocabulary : Set where
  field
    r : ℕ          -- Number of relational symbols
    R : Vect r ℕ -- Arities of relational symbols
    s : ℕ          -- Number of constant symbols

data RelationsFor : (size : ℕ) -> (r : ℕ) -> Vect r ℕ -> Set where
  RCons :
    {r r0 size : ℕ}
    {R : Vect r ℕ}
    -> (m : ℕ)
    -> Vect m (Vect r0 (Fin size))
    -> RelationsFor size r R
    -> RelationsFor size (suc r) (r0 :: R)
  RNil : {size : ℕ} -> RelationsFor size 0 empty

relationFor :
  { size r : ℕ } { R : Vect r ℕ }
  -> RelationsFor size r R
  -> (ri : Fin r)
  -> ℕ & (\m -> Vect m (Vect (indexVect ri R) (Fin size)))
relationFor (RCons m db rs) finzero = pair m db
relationFor (RCons m db rs) (finsuc u) = relationFor rs u


record Structure (v : Vocabulary) : Set where
  open Vocabulary
  field
    size : ℕ -- Size of the universe, which we assume to be the natural numbers up to the size, without loss of generality.
    relations : RelationsFor size (r v) (R v)
    constants : Vect (s v) (Fin size)

-- The graph with specified source and target
graphVocab : Vocabulary
graphVocab = x where
  open Vocabulary
  x : Vocabulary
  r x = 1
  R x = 2 :: empty
  s x = 2

-- The vocabulary of binary strings
binaryStrings : Vocabulary
binaryStrings = x where
  open Vocabulary
  x : Vocabulary
  r x = 2
  R x = 2 :: 1 :: empty
  s x = 0

data FO (v : Vocabulary) : Set where
  FO⊤ : FO v
  _FO=_ : ℕ -> ℕ -> FO v
  _FO∧_ : FO v -> FO v -> FO v
  FO¬ : FO v -> FO v
  FO∃ : ℕ -> FO v -> FO v
  FOR : (ri : Fin (Vocabulary.r v)) -> Vect (indexVect ri (Vocabulary.R v)) ℕ -> FO v

InterpretationInto : {vocab : Vocabulary} -> (structure : Structure vocab) -> Set
InterpretationInto structure = ℕ -> Fin (Structure.size structure)

extend :
  {v : Vocabulary }
  -> (A : Structure v)
  -> ℕ
  -> Fin (Structure.size A)
  -> InterpretationInto A
  -> InterpretationInto A
extend A v x i k = if k ==ℕ v then x else (i k)

truth : {v : Vocabulary} -> (structure : Structure v) -> InterpretationInto structure -> FO v -> 𝔹
truth A i FO⊤ = true
truth A i (v FO= w) = i v ==Fin i w
truth A i (a FO∧ b) = and (truth A i a) (truth A i b)
truth A i (FO¬ a) = not (truth A i a)
truth A i (FOR ri applied) =
  foldrVect (\xs -> or (eqVect _==Fin_ xs (mapVect i applied)))
    (snd (relationFor (Structure.relations A) ri))
    false
truth A i (FO∃ v a) =
  foldrVect (\x b -> and b (truth A (extend A v x i) a)) (indicesVect (Structure.size A)) false
