{-# OPTIONS --safe #-}

module Empty.Relations.Antisymmetric where

open import Agda.Primitive
open import Empty.Base
open import Relation.Antisymmetric.Set

instance
  ⊥Antisym : {A : Set} → Antisymmetric {lzero}{A} (λ _ _ → ⊥)
  ⊥Antisym = record { anti-sym = λ () }