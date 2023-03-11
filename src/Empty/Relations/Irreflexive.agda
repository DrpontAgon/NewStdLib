{-# OPTIONS --safe #-}

module Empty.Relations.Irreflexive where

open import Agda.Primitive
open import Empty.Base
open import Relation.Irreflexive.Set

instance
  ⊥Irrefl : {A : Set} → Irreflexive {lzero} {A} (λ _ _ → ⊥)
  ⊥Irrefl = record { irreflexive = λ z → z }