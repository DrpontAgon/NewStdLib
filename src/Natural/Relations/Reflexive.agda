{-# OPTIONS --safe #-}

module Natural.Relations.Reflexive where

open import Natural.Base
open import Relation.Reflexive.Set
open import Unit.Base.Type

instance
  ≤Refl : Reflexive _≤ℕ_
  ≤Refl = record { reflexive = λ where {a} → r {a} } where
    r : {a : ℕ} → a ≤ℕ a
    r {zero} = trivial
    r {suc a} = r {a}

  ≥Refl : Reflexive _≥ℕ_
  ≥Refl = record { reflexive = λ where {a} → r {a} } where
    r : {a : ℕ} → a ≥ℕ a
    r {zero} = trivial
    r {suc a} = r {a}
  
  ≡ℕRefl : Reflexive _≡ℕ_
  ≡ℕRefl = record { reflexive = λ where {a} → r {a} } where
    r : {a : ℕ} → a ≡ℕ a
    r {zero} = trivial
    r {suc a} = r {a}
  
  ≮Refl : Reflexive _≮ℕ_
  ≮Refl = record { reflexive = λ where {a} → r a } where
    r : (a : ℕ) → a ≮ℕ a
    r zero = λ z → z
    r (suc a) = r a

  ≯Refl : Reflexive _≯ℕ_
  ≯Refl = record { reflexive = λ where {a} → r a } where
    r : (a : ℕ) → a ≯ℕ a
    r zero = λ z → z
    r (suc a) = r a
  
  
reflℕ : {n : ℕ} → n ≡ℕ n
reflℕ {n} = reflexive {R = _≡ℕ_} {a = n}

infix 3 _∎ℕ _∎≤ℕ _∎≥ℕ

_∎ℕ : (x : ℕ) → x ≡ℕ x
x ∎ℕ = reflℕ {x}

_∎≤ℕ : (x : ℕ) → x ≤ℕ x
x ∎≤ℕ = reflexive {R = _≤ℕ_} {a = x}

_∎≥ℕ : (x : ℕ) → x ≥ℕ x
x ∎≥ℕ = reflexive {R = _≥ℕ_} {a = x}

elim-≡ℕ : ∀{x} (P : (y : ℕ) → x ≡ℕ y → Set) → P x (reflℕ {x}) →
          (y : ℕ) (x≡y : x ≡ℕ y) → P y x≡y
elim-≡ℕ {zero} P p zero x≡y = p
elim-≡ℕ {suc x} P p (suc y) x≡y = elim-≡ℕ {x} (λ y → P (suc y)) p y x≡y