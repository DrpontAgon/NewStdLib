{-# OPTIONS --safe #-}

module Unit.Base where

open import Empty.Base using (⊥)

record ⊤ : Set where
  inductive
  instance constructor trivial
open ⊤ public

{-# BUILTIN UNIT ⊤ #-}

infix 4 _≡⊤_ _≢⊤_

_≡⊤_ : ⊤ → ⊤ → Set
trivial ≡⊤ trivial = ⊤

_≢⊤_ : ⊤ → ⊤ → Set
trivial ≢⊤ trivial = ⊥