{-# OPTIONS --safe #-}

module Unit.Base.Functions where

open import Empty.Base.Type
open import Unit.Base.Type

infix 4 _≡⊤_ _≢⊤_

_≡⊤_ : ⊤ → ⊤ → Set
trivial ≡⊤ trivial = ⊤

_≢⊤_ : ⊤ → ⊤ → Set
trivial ≢⊤ trivial = ⊥