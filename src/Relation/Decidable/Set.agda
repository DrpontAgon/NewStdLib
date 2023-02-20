{-# OPTIONS --safe #-}

module Relation.Decidable.Set where

open import Agda.Builtin.Bool
open import Prelude.Set

private
  data Reflects {p} (P : Set p) : Bool → Set p where
    ofʸ : ( p :   P) → Reflects P true
    ofⁿ : (¬p : ¬ P) → Reflects P false

infix 2 _because_

record Dec {p} (P : Set p) : Set p where
  constructor _because_
  field
    does  : Bool
    proof : Reflects P does

open Dec public

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

recompute : ∀ {a} {A : Set a} → Dec A → .A → A
recompute (yes x) _ = x
recompute (no ¬p) x = exfalso (¬p x) irrelevant

-- Irrelevant : ∀ {p} → Set p → Set p
-- Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ₚ p₂