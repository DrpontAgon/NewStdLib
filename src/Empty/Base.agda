{-# OPTIONS --safe #-}

module Empty.Base where

-- open import Unit.Base using (⊤)

data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

exfalso_irrelevant : ∀ {i} {A : Set i} → .⊥ → A
exfalso_irrelevant ()

⊥-elim : ∀{i}{A : ⊥ → Set i} → (b : ⊥) → A b
⊥-elim ()

¬_ : ∀{i}(A : Set i) → Set i
¬ A = A → ⊥

¬ᵢ_ : ∀{ℓ}(A : Set ℓ) → Set ℓ
¬ᵢ A = ⦃ i : A ⦄ → ⊥

infixl 30 ¬_
infixl 30 ¬ᵢ_
{-
infix 4 _≡⊥_

_≡⊥_ : ⊥ → ⊥ → Set
_ ≡⊥ _ = ⊤
-}
weaken : ∀{i} → {A : Set i} → A → ¬ ¬ A
weaken a f = f a

contradiction : ∀{i}{j}{A : Set i}{B : Set j} → A → ¬ A → B
contradiction a ¬a = exfalso (¬a a)