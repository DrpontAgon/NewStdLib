{-# OPTIONS --safe #-}

module Relation.Reflexive.Set.Base where

record Reflexive {i} {A : Set i} (R : A → A → Set i) : Set i where
  field
    reflexive : {a : A} → R a a

open Reflexive {{...}} public