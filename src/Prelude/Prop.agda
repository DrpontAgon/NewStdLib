{-# OPTIONS --safe --prop #-}

module Prelude.Prop where

open import Agda.Primitive public

theₚ : ∀{i} → (A : Prop i) → A → A
theₚ _ x = x

syntax theₚ A x = x ∶ₚ A

typeOfₚ : ∀{i} → {A : Prop i} → A → Prop i
typeOfₚ {_} {A} _ = A

idₚ : ∀{i}{A : Prop i} → A → A
idₚ = λ z → z

infixr 11 _∘ₚ_
infixr 11 _⊚ₚ_

_∘ₚ_ : ∀{i j k}{A : Prop i}{B : Prop j}{C : Prop k}(f : B → C)(g : A → B)(x : A) → C
(f ∘ₚ g) x = f (g x)

_⊚ₚ_ : ∀ {i j k} {A : Prop i}{B : A → Prop j}{C : ∀ {x} → B x → Prop k}(f : ∀ {x} (y : B x) → C y)(g : (x : A) → B x)(x : A) → C (g x)
(f ⊚ₚ g) x = f (g x)

dflipₚ : ∀{i j k}{A : Prop i}{B : Prop j}{C : A → B → Prop k}
        (f : (x : A) → (y : B) → C x y) → (b : B) → (a : A) → C a b
dflipₚ f b a = f a b

flipₚ : ∀{i j k}{A : Prop i}{B : Prop j}{C : Prop k} → (A → B → C) → B → A → C
flipₚ = dflipₚ

constₚ : ∀{i j}{A : Prop i}{B : Prop j} → A → .B → A
constₚ = λ z _ → z

data ⊥ₚ : Prop where

exfalsoₚ : ∀{i}{A : Set i} → ⊥ₚ → A
exfalsoₚ ()

exfalsoₚ_irrelevant : ∀{i}{A : Set i} → .⊥ₚ → A
exfalsoₚ_irrelevant ()

exfalsoₚₚ : ∀{i}{A : Prop i} → ⊥ₚ → A
exfalsoₚₚ ()

exfalsoₚₚ_irrelevant : ∀{i}{A : Prop i} → .⊥ₚ → A
exfalsoₚₚ_irrelevant ()

record ⊤ₚ : Prop where
  inductive
  instance constructor trivialₚ
open ⊤ₚ public

¬ₚ_ : ∀{i}(A : Prop i) → Prop i
¬ₚ A = A → ⊥ₚ

infixl 30 ¬ₚ_

weakenₚ : ∀{i} → {A : Prop i} → A → ¬ₚ ¬ₚ A
weakenₚ a f = f a

contradictionₚ : ∀{i}{j}{A : Prop i}{B : Set j} → A → ¬ₚ A → B
contradictionₚ a ¬a = exfalsoₚ (¬a a)

contradictionₚₚ : ∀{i}{j}{A : Prop i}{B : Prop j} → A → ¬ₚ A → B
contradictionₚₚ a ¬a = exfalsoₚₚ (¬a a)