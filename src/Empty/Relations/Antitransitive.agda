{-# OPTIONS --safe #-}

module Empty.Relations.Antitransitive where

open import Agda.Primitive
open import Empty.Base
open import Relation.Antitransitive.Set

instance
  ⊥Antitrans : {A : Set} → Antitransitive {lzero}{A} (λ _ _ → ⊥)
  ⊥Antitrans = record { anti-trans = λ _ _ z → z }