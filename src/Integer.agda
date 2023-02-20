{-# OPTIONS --prop --rewriting #-}

module Integer where

import Natural as N

data ℤ : Set where
  pos : N.ℕ → ℤ
  negsuc : N.ℕ → ℤ

{-# BUILTIN INTEGER ℤ #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

{-
infixl 6 _+_

_+_ : ℤ → ℤ → ℤ
pos x + pos y = pos (x N.+ y)
pos x + negsuc y = {!    !}
negsuc x + pos y = {!   !}
negsuc x + negsuc y = negsuc (N.suc (x N.+ y))
-}