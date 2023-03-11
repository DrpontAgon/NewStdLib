{-# OPTIONS --prop --safe #-}

module Relation.Universal.Prop.Base where

record Universalₚ {i}{A : Set i}(R : A → A → Prop i) : Prop i where
  field
    universalₚ : {a b : A} → R a b

open Universalₚ {{...}} public