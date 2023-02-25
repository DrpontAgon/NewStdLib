{-# OPTIONS --safe #-}

module Relation.Asymmetric.Set where

open import Empty.Base

record Asymmetric {i} {A : Set i} (R : A → A → Set i) : Set i where
  field
    asym : {x y : A} → R x y → ¬ R y x

open Asymmetric {{...}} public