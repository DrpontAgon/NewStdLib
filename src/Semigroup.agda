{-# OPTIONS --prop --rewriting #-}

module Semigroup where

open import Prelude

record Semigroup (A : Set) (_<>_ : A → A → A) : Set where
  field
    assoc : {x y z : A} → (x <> y) <> z ≡ x <> (y <> z)

instance
  Semigroupℕ+ : Semigroup ℕ (_+_)
  Semigroupℕ+ = record { assoc = λ {x} → ≡ₛ→≡ (assoc+ {x}) }

instance
  Semigroupℕ* : Semigroup ℕ (_*_)
  Semigroupℕ* = record { assoc = λ {x} → ≡ₛ→≡ (assoc* {x}) }