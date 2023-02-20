{-# OPTIONS --prop --rewriting #-}

module Either where

open import Prelude public
open import Agda.Primitive public

data _⊎_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  ι₁ : A → A ⊎ B
  ι₂ : B → A ⊎ B

infixl 2 _⊎_

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
       (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (ι₁ t) u v = u t
case (ι₂ t) u v = v t

Dec : ∀{i}(A : Set i) → Set i
Dec A = A ⊎ ¬ A