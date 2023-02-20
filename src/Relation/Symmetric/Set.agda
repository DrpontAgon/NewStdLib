{-# OPTIONS --safe #-}

module Relation.Symmetric.Set where

record Symmetric {i} {A : Set i} (R : A → A → Set i) : Set i where
  field
    sym : {x y : A} → R x y → R y x

open Symmetric {{...}} public