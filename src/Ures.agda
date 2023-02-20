module Ures where

open import Data.Nat
open import Data.Sum
open import Relation.Nullary

max : ℕ → ℕ → ℕ
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

iteList : {A B : Set} → (A → B → B) → B → List A → B
iteList _ b [] = b
iteList f b (x ∷ xs) = f x (iteList f b xs)

data Tree : Set where
  node : List Tree → Tree

{-# TERMINATING #-}
height : Tree → ℕ
height (node []) = 1
height (node l@(_ ∷ _)) = suc (iteList (λ t acc → max (height t) acc) 0 l)

tr : Tree -- 3
tr = node (node [] ∷ node (node [] ∷ []) ∷ node [] ∷ [])

tr2 : Tree -- 4
tr2 = node (node [] ∷ node (node [] ∷ []) ∷ node (node (node [] ∷ []) ∷ []) ∷ [])

pr : ℕ
pr = height tr2

AnotDecidable : ∀{i}{A : Set i} → ¬ ¬ (A ⊎ ¬ A)
AnotDecidable f = f (inj₂ (λ a → f (inj₁ a)))