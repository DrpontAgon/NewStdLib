{-# OPTIONS --prop #-}

module Irreflexive where

open import Prelude
open import Reflexive

record Irreflexive {i} {A : Set i} (R : A → A → Set i) : Set i where
  field
    irreflexive : {a : A} → ¬ R a a

open Irreflexive {{...}} public

record Irreflexiveₚ {i} {A : Set i} (R : A → A → Prop i) : Prop i where
  field
    irreflexiveₚ : {a : A} → ¬ₚ R a a

open Irreflexiveₚ {{...}} public

Refl→¬Irrefl : ∀{i} → {A : Set i} → {a : A} → {R : A → A → Set i} 
             → {{r : Reflexive R}} → ¬ Irreflexive R
Refl→¬Irrefl {i} {A} {a} {R}
  ⦃ r = record { reflexive = reflexive } ⦄ 
  record { irreflexive = irreflexive } = irreflexive {a} reflexive

Irrefl→¬Refl : ∀{i} → {A : Set i} → {a : A} → {R : A → A → Set i}
             → {{r : Irreflexive R}} → ¬ Reflexive R
Irrefl→¬Refl {i} {A} {a} {R}
  ⦃ r = record { irreflexive = irreflexive } ⦄ 
  record { reflexive = reflexive } = irreflexive {a} reflexive