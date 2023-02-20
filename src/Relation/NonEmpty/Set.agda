{-# OPTIONS --safe #-}

module Relation.NonEmpty.Set where

record NonEmpty {i}{A : Set i}(R : A → A → Set i) : Set i where
  field
    {x} : A
    {y} : A
    proof : R x y

open NonEmpty {{...}} public