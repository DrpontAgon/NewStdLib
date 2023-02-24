{-# OPTIONS --safe #-}

module Unit.Base.Type where

record ⊤ : Set where
  inductive
  instance constructor trivial
open ⊤ public

{-# BUILTIN UNIT ⊤ #-}