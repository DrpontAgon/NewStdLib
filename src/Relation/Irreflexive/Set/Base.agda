{-# OPTIONS --safe #-}

module Relation.Irreflexive.Set.Base where

open import Empty.Base.Functions

record Irreflexive {i}{A : Set i}(R : A → A → Set i) : Set i where
  field
    irreflexive : {a : A} → ¬ (R a a)

open Irreflexive {{...}} public