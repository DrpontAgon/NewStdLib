{-# OPTIONS --safe #-}

module Empty.Relations.Symmetric where

open import Agda.Primitive
open import Empty.Base
open import Relation.Symmetric.Set

instance
  ⊥Sym : {A : Set} → Symmetric {lzero}{A} (λ _ _ → ⊥)
  ⊥Sym = record { sym = λ z → z }