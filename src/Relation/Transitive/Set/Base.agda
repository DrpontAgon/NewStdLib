{-# OPTIONS --safe #-}

module Relation.Transitive.Set.Base where

record Transitive {i} {A : Set i} (R : A → A → Set i) : Set i where
  field
    trans : {x y z : A} → R x y → R y z → R x z

  infixr 2 _R⟨_⟩_
  _R⟨_⟩_ : (x : A) → {y z : A} → R x y → R y z → R x z
  x R⟨ Rxy ⟩ Ryz = trans Rxy Ryz

open Transitive {{...}} public