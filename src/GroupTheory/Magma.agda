{-# OPTIONS --rewriting --prop #-}
module GroupTheory.Magma where

record Magma {i}(A : Set i) : Set i where
  constructor mkMagma
  field
    _⊕_ : A → A → A

record Magmaₚ {i}{A : Prop i} : Prop i where
  constructor mkMagmaₚ
  field
    _⊕ₚ_ : A → A → A

open Magma public
open Magmaₚ public
