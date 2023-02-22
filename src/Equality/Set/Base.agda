{-# OPTIONS --safe #-}

module Equality.Set.Base where

-- Számelmélet: oszthatóság kell, mókás

-- open import Transitive
-- open import Symmetric
-- open import Reflexive
open import Prelude.Set
open import Agda.Primitive
open import Empty.Base

infix 0 _≡_ _≢_

data _≡_ {i}{A : Set i}(x : A) : A → Set i where
  instance refl : x ≡ x

_≢_ : ∀{i}{A : Set i} → A → A → Set i
x ≢ y = ¬ (x ≡ y)

subst : ∀{i j}{A : Set i}(B : A → Set j){a a' : A} → a ≡ a' → B a → B a'
subst B refl b = b

substrefl : ∀{i j}{A : Set i}(B : A → Set j){a : A}{a= : a ≡ a}{b : B a} → subst B a= b ≡ b
substrefl {i} {j} {A} B {a} {refl} {b} = refl

happly : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
happly refl _ = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

infix 3 _∎

_∎ : ∀{ℓ}{A : Set ℓ}(x : A) → x ≡ x
x ∎ = refl {x = x}

{-
postulate
  funExt : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
  funExtₛ : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} → (∀ x → f x ≡ₛ g x) → f ≡ₛ g
  funExtId1 : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} → (λ x → funExtₛ {i} {j} {A} {B} {f} {g} (happlyₛ x)) ≡ (λ x → x)
  funExtId2 : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} → (λ x → happlyₛ (funExtₛ {i} {j} {A} {B} {f} {g} x)) ≡ (λ x → x)

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

congₛ : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a a' : A} → a ≡ₛ a' → f a ≡ₛ f a'
congₛ f reflₛ = reflₛ

infix 3 _∎
infix 3 _∎ₛ

_∎ : ∀{ℓ}{A : Set ℓ}(x : A) → x ≡ x
x ∎ = refl {x = x}

_∎ₛ : ∀{ℓ}{A : Set ℓ}(x : A) → x ≡ₛ x
x ∎ₛ = reflₛ {x = x}

instance
  ≡ₛTrans : ∀{i A} → Transitive {i} {A} _≡ₛ_
  ≡ₛTrans = record { trans = λ {reflₛ reflₛ → reflₛ} }

  ≡Trans : ∀{i A} → Transitiveₚ {i} {A} _≡_
  ≡Trans = record { transₚ = λ {refl refl → refl} }

infixr 2 _≡⟨_⟩_
infixr 2 _≡⟨_⟩ₛ_

_≡⟨_⟩_ : ∀{i} → {A : Set i} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ y ⟩ z = transₚ {x = x} y z

_≡⟨_⟩ₛ_ : ∀{i} → {A : Set i} → (x : A) → {y z : A} → x ≡ₛ y → y ≡ₛ z → x ≡ₛ z
x ≡⟨ y ⟩ₛ z = trans {x = x} y z

instance
  ≡ₛRefl : ∀{i A} → Reflexive {i} {A} _≡ₛ_
  ≡ₛRefl = record { reflexive = reflₛ }

  ≡Refl : ∀{i A} → Reflexiveₚ {i} {A} _≡_
  ≡Refl = record { reflexiveₚ = refl }

instance
  ≡ₛSym : ∀{i A} → Symmetric {i} {A} _≡ₛ_ 
  ≡ₛSym = record { sym = λ {reflₛ → reflₛ} }

  ≡Sym : ∀{i A} → Symmetricₚ {i} {A} _≡_ 
  ≡Sym = record { symₚ = λ {refl → refl} }
-}

lhs : ∀{i}{A : Set i}{x y : A} → .(x ≡ y) → A
lhs {x = x} _ = x

rhs : ∀{i}{A : Set i}{x y : A} → .(x ≡ y) → A
rhs {y = y} _ = y
