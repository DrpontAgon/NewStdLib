{-# OPTIONS --safe #-}

module Empty.Relations.Asymmetric where

open import Agda.Primitive
open import Empty.Base
open import Relation.Asymmetric.Set

instance
  ⊥Asym : {A : Set} → Asymmetric {lzero}{A} (λ _ _ → ⊥)
  ⊥Asym = record { asym = λ _ z → z }