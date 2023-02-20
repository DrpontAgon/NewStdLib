{-# OPTIONS --prop --safe #-}

module Relation.Asymmetric.Prop where

open import Prelude.Prop

record Asymmetricₚ {i} {A : Set i} (R : A → A → Prop i) : Prop i where
  field
    asymₚ : {x y : A} → R x y → ¬ₚ R y x

open Asymmetricₚ {{...}} public