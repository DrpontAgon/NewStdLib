{-# OPTIONS --prop --rewriting #-}

module Main where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import FunctorApplicativeSelectiveMonad

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

main : IO ⊤
main = putStrLn "alma"