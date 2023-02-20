{-# OPTIONS --prop --rewriting #-}

module Foldable where

{-
Törvények:

foldr f z t = appEndo (foldMap (Endo . f) t ) z
foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z
fold = foldMap id
-}

