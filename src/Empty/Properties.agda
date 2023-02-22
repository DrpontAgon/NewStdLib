{-# OPTIONS --safe #-}

module Empty.Properties where

open import Unit.Base using (⊤ ; trivial)
open import Empty.Base
open import Relation.Decidable.Set

Decidable≡⊥ : {x y : ⊥} → Dec (x ≡⊥ y)
Decidable≡⊥ = yes trivial

instance
  ¬ᵢ⊥ : ¬ᵢ ⊥
  ¬ᵢ⊥ ⦃ i ⦄ = i