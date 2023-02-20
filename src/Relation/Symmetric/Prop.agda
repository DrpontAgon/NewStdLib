{-# OPTIONS --prop --safe #-}

module Relation.Symmetric.Prop where

record Symmetricₚ {i} {A : Set i} (R : A → A → Prop i) : Prop i where
  field
    symₚ : {x y : A} → R x y → R y x

open Symmetricₚ {{...}} public