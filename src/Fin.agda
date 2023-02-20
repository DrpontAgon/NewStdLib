{-# OPTIONS --prop --rewriting #-}

module Fin where

open import Natural
open import Equality
open import Prelude
open import Symmetric

data Fin {i} : ℕ → Set i where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin {i} n → Fin (suc n)

{-# INJECTIVE Fin #-}