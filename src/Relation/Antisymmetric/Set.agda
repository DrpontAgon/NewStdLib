{-# OPTIONS --safe #-}

module Relation.Antisymmetric.Set where

open import Agda.Primitive
open import Equality.Set.Base

record Antisymmetric {i} {A : Set i} (R : A → A → Set i) : Set i where
  field
    anti-sym : {x y : A} → R x y → R y x → x ≡ y

open Antisymmetric {{...}} public