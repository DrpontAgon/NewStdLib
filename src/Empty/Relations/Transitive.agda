{-# OPTIONS --safe #-}

module Empty.Relations.Transitive where

open import Relation.Transitive.Set
open import Empty.Base

instance
  ⊥Trans : {A : Set} → Transitive {_}{A} (λ _ _ → ⊥)
  ⊥Trans = record { trans = λ _ z → z }