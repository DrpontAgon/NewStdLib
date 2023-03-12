{-# OPTIONS --safe #-}

module Relation.Antitransitive.Set.Base where

open import Empty.Base

record Antitransitive {i} {A : Set i} (R : A → A → Set i) : Set i where
  field
    anti-trans : {a b : A} → R a b → {c : A} → R b c → ¬ R a c

open Antitransitive {{...}} public