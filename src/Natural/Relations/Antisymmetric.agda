{-# OPTIONS --safe #-}

module Natural.Relations.Antisymmetric where

open import Natural.Base
open import Unit.Base
open import Empty.Base
open import Equality.Set.Base
open import Relation.Antisymmetric.Set

instance
  ≤ℕAntisym : Antisymmetric _≤ℕ_
  ≤ℕAntisym = record { anti-sym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a ≤ℕ b → b ≤ℕ a → a ≡ b
    r zero zero a≤b b≤a = refl
    r (suc a) (suc b) a≤b b≤a = cong suc (r a b a≤b b≤a)

  ≥ℕAntisym : Antisymmetric _≥ℕ_
  ≥ℕAntisym = record { anti-sym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a ≥ℕ b → b ≥ℕ a → a ≡ b
    r zero zero a≥b b≥a = refl
    r (suc a) (suc b) a≥b b≥a = cong suc (r a b a≥b b≥a)

  ≮ℕAntisym : Antisymmetric _≮ℕ_
  ≮ℕAntisym = record { anti-sym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a ≮ℕ b → b ≮ℕ a → a ≡ b
    r zero zero a≮b b≮a = refl
    r zero (suc b) a≮b b≮a = exfalso (a≮b trivial)
    r (suc a) zero a≮b b≮a = exfalso (b≮a trivial)
    r (suc a) (suc b) a≮b b≮a = cong suc (r a b a≮b b≮a)

  ≯ℕAntisym : Antisymmetric _≯ℕ_
  ≯ℕAntisym = record { anti-sym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a ≯ℕ b → b ≯ℕ a → a ≡ b
    r zero zero a≯b b≯a = refl
    r zero (suc b) a≯b b≯a = exfalso (b≯a trivial)
    r (suc a) zero a≯b b≯a = exfalso (a≯b trivial)
    r (suc a) (suc b) a≯b b≯a = cong suc (r a b a≯b b≯a)
  
  ≡ℕAntisym : Antisymmetric _≡ℕ_
  ≡ℕAntisym = record { anti-sym = λ where {x} {y} → r x y } where
    r : (a b : ℕ) → a ≡ℕ b → b ≡ℕ a → a ≡ b
    r zero zero a≡b b≡a = refl
    r (suc a) (suc b) a≡b b≡a = cong suc (r a b a≡b b≡a)