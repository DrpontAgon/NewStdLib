{-# OPTIONS --safe #-}

module Relation.MiscProperties.Set where

open import Relation.Symmetric.Set
open import Relation.Antisymmetric.Set
open import Relation.Asymmetric.Set
open import Relation.NonEmpty.Set
open import Relation.Reflexive.Set.Base
open import Prelude.Set

instance
  Asym→Antisym : ∀{i}{A : Set i}{R : A → A → Set i} →
                 ⦃ r : Asymmetric R ⦄ → Antisymmetric R
  Asym→Antisym ⦃ r ⦄ = record
    { anti-sym = λ r1 r2 → exfalso (asym r1 r2) }

  ¬Antisym→¬Asym : ∀{i}{A : Set i}{R : A → A → Set i} →
                   ⦃ ¬ᵢ Antisymmetric R ⦄ → ¬ᵢ Asymmetric R
  ¬Antisym→¬Asym ⦃ ¬r ⦄ ⦃ a ⦄ = ¬r ⦃ Asym→Antisym ⦃ a ⦄ ⦄

  Sym→¬Asym : ∀{i}{A : Set i}{R : A → A → Set i} → ⦃ e : NonEmpty R ⦄ →
              ⦃ r : Symmetric R ⦄ → ¬ᵢ Asymmetric R
  Sym→¬Asym ⦃ e = record { proof = e } ⦄ ⦃ r = record { sym = sym } ⦄ ⦃ record { asym = asym } ⦄ =
    asym e (sym e)

  Asym→¬Sym : ∀{i}{A : Set i}{R : A → A → Set i} → ⦃ e : NonEmpty R ⦄ →
              ⦃ r : Asymmetric R ⦄ → ¬ᵢ Symmetric R
  Asym→¬Sym ⦃ e = record { proof = proof } ⦄ ⦃ record { asym = asym } ⦄ ⦃ record { sym = sym } ⦄ =
    asym proof (sym proof)