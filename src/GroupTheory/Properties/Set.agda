{-# OPTIONS --rewriting #-}
module GroupTheory.Properties.Set where

open import Equality.Set

record Medial {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    med : ∀ x y u z → (x ⊕ y) ⊕ (u ⊕ z) ≡ (x ⊕ u) ⊕ (y ⊕ z)

record Semimedial {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    -- TODO: Split in two
    leftsemi  : ∀ x y z → (x ⊕ x) ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ (x ⊕ z)
    rightsemi : ∀ x y z → (y ⊕ z) ⊕ (x ⊕ x) ≡ (y ⊕ x) ⊕ (z ⊕ x)

record Autodistributive {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    -- TODO: Split in two
    leftdistrib  : ∀ x y z → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ (x ⊕ z)
    rightdistrib : ∀ x y z → (y ⊕ z) ⊕ x ≡ (y ⊕ x) ⊕ (z ⊕ x)

record Associative {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    assoc : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)

record Commutative {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    comm : ∀ a b → a ⊕ b ≡ b ⊕ a

record Idempotent {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    idem : ∀ x → x ⊕ x ≡ x

record Unipotent {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    unip : ∀ x y → x ⊕ x ≡ y ⊕ y

record Zeropotent {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    zerop₁ : ∀ x y → (x ⊕ x) ⊕ y ≡ (x ⊕ x)
    zerop₂ : ∀ x y → y ⊕ (x ⊕ x) ≡ (x ⊕ x)

record Flexible {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    flex : ∀ x y → (x ⊕ y) ⊕ x ≡ x ⊕ (y ⊕ x)

record Unital {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    ε : A
    unitl : ∀ x → x ⊕ ε ≡ x
    unitr : ∀ x → ε ⊕ x ≡ x

record Cancellative {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    -- TODO: Split in two
    leftc  : ∀ x y z → (x ⊕ y) ≡ (x ⊕ z) → y ≡ z
    rightc : ∀ x y z → (y ⊕ x) ≡ (z ⊕ x) → y ≡ z

open Medial public
open Semimedial public
open Autodistributive public
open Associative public
open Commutative public
open Idempotent public
open Unipotent public
open Zeropotent public
open Flexible public
open Unital public
open Cancellative public
