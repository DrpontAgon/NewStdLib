{-# OPTIONS --prop --safe #-}

module Relation.NonEmpty.Prop where

open import Agda.Primitive

record NonEmptyₚ {i}{A : Prop i}(R : A → A → Prop i) : Prop i where
  field
    {xₚ} : A
    {yₚ} : A
    proofₚ : R xₚ yₚ

open NonEmptyₚ {{...}} public