{-# OPTIONS --safe #-}

module Unit.Properties where

open import Unit.Base
open import Relation.Decidable.Set

Decidable≡⊤ : {x y : ⊤} → Dec (x ≡⊤ y)
Decidable≡⊤ = yes trivial