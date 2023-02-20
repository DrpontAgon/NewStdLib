{-# OPTIONS --safe #-}

module Prelude.Set where

open import Agda.Primitive public

the : ∀{i} → (A : Set i) → A → A
the _ x = x

syntax the A x = x ∶ A

typeOf : ∀{i} → {A : Set i} → .A → Set i
typeOf {_} {A} _ = A

id : ∀{i}{A : Set i} → A → A
id = λ z → z

infixr 11 _∘_
infixr 11 _⊚_

_∘_ : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}(f : B → C)(g : A → B)(x : A) → C
(f ∘ g) x = f (g x)

_⊚_ : ∀ {i j k} {A : Set i}{B : A → Set j}{C : ∀ {x} → B x → Set k}(f : ∀ {x} (y : B x) → C y)(g : (x : A) → B x)(x : A) → C (g x)
(f ⊚ g) x = f (g x)

dflip : ∀{i j k}{A : Set i}{B : Set j}{C : A → B → Set k}
        (f : (x : A) → (y : B) → C x y) → (b : B) → (a : A) → C a b
dflip f b a = f a b

flip : ∀{i j k}{A : Set i}{B : Set j}{C : Set k} → (A → B → C) → B → A → C
flip = dflip

const : ∀{i j}{A : Set i}{B : Set j} → A → .B → A
const = λ z _ → z

record Σ {i}{j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
  inductive
  constructor _,Σ_
  field
    π₁ : A
    π₂ : B π₁
open Σ public

infixr 20 _×_ _,_ _,Σ_

_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B

_,_ : ∀{i j}{A : Set i}{B : Set j} → A → B → A × B
a , b = a ,Σ b

infix -1 Σ
syntax Σ X (λ x → Y) = ∃ x ∈ X ∣ Y

_↔_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

exfalso_irrelevant : ∀ {i} {A : Set i} → .⊥ → A
exfalso_irrelevant ()

record ⊤ : Set where
  inductive
  instance constructor trivial
open ⊤ public

¬_ : ∀{i}(A : Set i) → Set i
¬ A = A → ⊥

¬ᵢ_ : ∀{ℓ}(A : Set ℓ) → Set ℓ
¬ᵢ A = ⦃ i : A ⦄ → ⊥

infixl 30 ¬_
infixl 30 ¬ᵢ_

instance
  ¬ᵢ⊥ : ¬ᵢ ⊥
  ¬ᵢ⊥ ⦃ i ⦄ = i

weaken : ∀{i} → {A : Set i} → A → ¬ ¬ A
weaken a f = f a

contradiction : ∀{i}{j}{A : Set i}{B : Set j} → A → ¬ A → B
contradiction a ¬a = exfalso (¬a a)

{-
impossible : ∀{i} → {A : Set i} → ¬ ¬ A → A
impossible f = ?
-}

record Endo {i} (A : Set i) : Set i where
  constructor mkEndo
  field
    endo : A → A

record Dual {i} (A : Set i) : Set i where
  constructor mkDual
  field
    dual : A