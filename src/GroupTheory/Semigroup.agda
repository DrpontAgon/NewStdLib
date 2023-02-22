{-# OPTIONS --rewriting --prop #-}

module GroupTheory.Semigroup where

open import GroupTheory.Properties.Set public
open import Equality.Set.Base public

import GroupTheory.Magma

record Semigroup {i}(A : Set i) : Set i where
  constructor mkSemigroup
  field
    { magma } : GroupTheory.Magma.Magma A

  _⊕_ : A → A → A
  _⊕_ = GroupTheory.Magma._⊕_ magma

  field
    assoc⊕ : Associative (_⊕_)

  flexSG : Flexible (_⊕_)
  flexSG = record { flex = λ x y → assoc assoc⊕ x y x }

open Semigroup public
