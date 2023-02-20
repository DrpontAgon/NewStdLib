{-# OPTIONS --rewriting #-}

module Equality.Set.BuiltinDeclarations where

open import Equality.Set.Base

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}