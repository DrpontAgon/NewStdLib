{-# OPTIONS --prop #-}

module Relation.Antisymmetric.Prop where

open import Agda.Primitive
open import Equality.Prop.Base

record Antisymmetricₚ {i} {A : Set i} (R : A → A → Prop i) : Prop i where
  field
    anti-symₚ : {x y : A} → R x y → R y x → x ≡ₚ y

open Antisymmetricₚ {{...}} public