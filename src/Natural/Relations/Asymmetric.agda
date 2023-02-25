{-# OPTIONS --safe #-}

module Natural.Relations.Asymmetric where

open import Natural.Base
open import Unit.Base
open import Empty.Base
open import Relation.Asymmetric.Set

instance
  <ℕAsym : Asymmetric _<ℕ_
  <ℕAsym = record { asym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a <ℕ b → ¬ (b <ℕ a)
    r (suc a) (suc b) a<b b<a = r b a b<a a<b

  >ℕAsym : Asymmetric _>ℕ_
  >ℕAsym = record { asym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a >ℕ b → ¬ (b >ℕ a)
    r (suc a) (suc b) a>b b<a = r a b a>b b<a
  
  ≰ℕAsym : Asymmetric _≰ℕ_
  ≰ℕAsym = record { asym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a ≰ℕ b → ¬ (b ≰ℕ a)
    r zero b a≰b b≰a = a≰b trivial
    r (suc a) zero a≰b b≰a = b≰a trivial
    r (suc a) (suc b) a≰b b≰a = r a b a≰b b≰a

  ≱ℕAsym : Asymmetric _≱ℕ_
  ≱ℕAsym = record { asym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a ≱ℕ b → ¬ (b ≱ℕ a)
    r zero b a≱b b≱a = b≱a trivial
    r (suc a) zero a≱b b≱a = a≱b trivial
    r (suc a) (suc b) a≱b b≱a = r a b a≱b b≱a