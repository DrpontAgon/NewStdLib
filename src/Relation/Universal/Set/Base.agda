{-# OPTIONS --safe #-}

module Relation.Universal.Set.Base where

record Universal {i}{A : Set i}(R : A → A → Set i) : Set i where
  field
    universal : {a b : A} → R a b

open Universal {{...}} public