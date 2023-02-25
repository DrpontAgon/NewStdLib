{-# OPTIONS --safe #-}

module Natural.Relations.Irreflexive where

open import Natural.Base
open import Empty.Base
open import Unit.Base
open import Relation.Irreflexive.Set

instance
  <ℕIrrefl : Irreflexive _<ℕ_
  <ℕIrrefl = record { irreflexive = λ where {a} → r a } where
    r : (a : ℕ) → ¬ (a <ℕ a)
    r (suc a) a<a = r a a<a

  >ℕIrrefl : Irreflexive _>ℕ_
  >ℕIrrefl = record { irreflexive = λ where {a} → r a } where
    r : (a : ℕ) → ¬ (a >ℕ a)
    r (suc a) a>a = r a a>a
  
  ≢ℕIrrefl : Irreflexive _≢ℕ_
  ≢ℕIrrefl = record { irreflexive = λ where {a} → r a } where
    r : (a : ℕ) → ¬ (a ≢ℕ a)
    r (suc a) a≢a = r a a≢a
  
  ≰ℕIrrefl : Irreflexive _≰ℕ_
  ≰ℕIrrefl = record { irreflexive = λ where {a} → r a } where
    r : (a : ℕ) → ¬ (a ≰ℕ a)
    r zero a≤a = a≤a trivial
    r (suc a) a≤a = r a a≤a

  ≱ℕIrrefl : Irreflexive _≱ℕ_
  ≱ℕIrrefl = record { irreflexive = λ where {a} → r a } where
    r : (a : ℕ) → ¬ (a ≱ℕ a)
    r zero a≥a = a≥a trivial
    r (suc a) a≥a = r a a≥a