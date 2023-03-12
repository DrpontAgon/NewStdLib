{-# OPTIONS --prop --safe #-}

module Relation.Reflexive.Prop.Base where

record Reflexiveₚ {i} {A : Set i} (R : A → A → Prop i) : Prop i where
  field
    reflexiveₚ : {a : A} → R a a

open Reflexiveₚ {{...}} public