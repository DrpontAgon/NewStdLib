{-# OPTIONS --prop --safe #-}

module Relation.Irreflexive.Prop.Base where

-- Kell ⊥ : Prop
-- Most még csak Set-es van.

{-
open import Empty.Base.Functions

record Irreflexive {i}{A : Set i}(R : A → A → Set i) : Set i where
  field
    irreflexive : {a : A} → ¬ (R a a)

open Irreflexive {{...}} public
-}