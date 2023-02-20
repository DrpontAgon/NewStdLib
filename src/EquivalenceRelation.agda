{-# OPTIONS --prop #-}

module EquivalenceRelation where

open import Transitive
open import Reflexive
open import Symmetric

record EquivalenceRelation {i} {A : Set i} (R : A → A → Set i) 
  {{t : Transitive {i} {A} R}} {{r : Reflexive {i} {A} R}} {{s : Symmetric {i} {A} R}} : Set i where

open EquivalenceRelation {{...}} public

record EquivalenceRelationₚ {i} {A : Set i} (R : A → A → Prop i) 
  {{t : Transitiveₚ {i} {A} R}} {{r : Reflexiveₚ {i} {A} R}} {{s : Symmetricₚ {i} {A} R}} : Prop i where

open EquivalenceRelationₚ {{...}} public