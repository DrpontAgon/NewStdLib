{-# OPTIONS --safe --prop #-}

module Relation.Transitive.Prop.Base where

record Transitiveₚ {i} {A : Set i} (R : A → A → Prop i) : Prop i where
  field
    transₚ : {x y z : A} → R x y → R y z → R x z

  infixr 2 _R⟨_⟩ₚ_
  _R⟨_⟩ₚ_ : (x : A) → {y z : A} → R x y → R y z → R x z
  x R⟨ Rxy ⟩ₚ Ryz = transₚ Rxy Ryz

open Transitiveₚ {{...}} public