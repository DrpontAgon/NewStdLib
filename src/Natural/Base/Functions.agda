{-# OPTIONS --safe #-}

module Natural.Base.Functions where

open import Natural.Base.Type
open import Unit.Base.Type
open import Empty.Base
open import Agda.Builtin.Nat
  hiding (Nat)
  renaming (_-_ to _-unsafe_ ; _<_ to _<ᵇ_)
  public

infix 4 _≡ℕ_ _≢ℕ_ _<ℕ_ _>ℕ_ _≤ℕ_ _≥ℕ_ _≮ℕ_ _≯ℕ_ _≰ℕ_ _≱ℕ_

_≡ℕ_ : ℕ → ℕ → Set
zero ≡ℕ zero = ⊤
zero ≡ℕ suc m = ⊥
suc n ≡ℕ zero = ⊥
suc n ≡ℕ suc m = n ≡ℕ m

_≢ℕ_ : ℕ → ℕ → Set
zero ≢ℕ zero = ⊥
zero ≢ℕ suc m = ⊤
suc n ≢ℕ zero = ⊤
suc n ≢ℕ suc m = n ≢ℕ m

_≤ℕ_ : ℕ → ℕ → Set
zero ≤ℕ m = ⊤
suc n ≤ℕ zero = ⊥
suc n ≤ℕ suc m = n ≤ℕ m

_<ℕ_ : ℕ → ℕ → Set
n <ℕ m = suc n ≤ℕ m

_>ℕ_ : ℕ → ℕ → Set
n >ℕ m = m <ℕ n

_≥ℕ_ : ℕ → ℕ → Set
n ≥ℕ m = m ≤ℕ n

_≮ℕ_ : ℕ → ℕ → Set
n ≮ℕ m = ¬ (n <ℕ m)

_≯ℕ_ : ℕ → ℕ → Set
n ≯ℕ m = ¬ (n >ℕ m)

_≰ℕ_ : ℕ → ℕ → Set
n ≰ℕ m = ¬ (n ≤ℕ m)

_≱ℕ_ : ℕ → ℕ → Set
n ≱ℕ m = ¬ (n ≥ℕ m)

NonZero : ℕ → Set
NonZero zero    = ⊥
NonZero (suc x) = ⊤

instance
  ≢-nonZero : ∀ {n} → ⦃ n ≢ℕ 0 ⦄ → NonZero n
  ≢-nonZero {suc n} = trivial

  >-nonZero : ∀ {n} → ⦃ n >ℕ 0 ⦄ → NonZero n
  >-nonZero {suc n} = trivial

  <-nonZero : ∀ {n} → ⦃ 0 <ℕ n ⦄ → NonZero n
  <-nonZero {suc n} = trivial

IsEven : ℕ → Set
IsEven 0 = ⊤
IsEven 1 = ⊥
IsEven (suc (suc n)) = IsEven n

IsOdd : ℕ → Set
IsOdd 0 = ⊥
IsOdd 1 = ⊤
IsOdd (suc (suc n)) = IsOdd n

infixl 6 _-_

pred : (n : ℕ) → ⦃ n >ℕ 0 ⦄ → ℕ
pred (suc n) = n

_-_ : (x : ℕ) → (y : ℕ) → ⦃ y ≤ℕ x ⦄ → ℕ
x - zero = x
(suc x - suc y) = x - y

max : (x y : ℕ) → ℕ
max zero y = y
max (suc x) zero = suc x
max (suc x) (suc y) = suc (max x y)

min : (x y : ℕ) → ℕ
min zero y = zero
min (suc x) zero = zero
min (suc x) (suc y) = suc (min x y)

⌊_/2⌋ : ℕ → ℕ
⌊ 0 /2⌋           = 0
⌊ 1 /2⌋           = 0
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

⌈_/2⌉ : ℕ → ℕ
⌈ n /2⌉ = ⌊ suc n /2⌋

_^_ : (x n : ℕ) → ⦃ x + n ≢ℕ 0 ⦄ → ℕ
(suc x ^ 0) = 1
(0 ^ suc n) = 0
(y@(suc x) ^ suc n) = y * (y ^ n)

∣_-_∣ : ℕ → ℕ → ℕ
∣ zero  - y     ∣ = y
∣ suc x - zero  ∣ = suc x
∣ suc x - suc y ∣ = ∣ x - y ∣

recℕ : ∀{i}{A : Set i} → (A → A) → A → ℕ → A
recℕ f a zero = a
recℕ f a (suc n) = f (recℕ f a n)

indℕ : ∀{ℓ}(A : ℕ → Set ℓ)(z : A zero)(s : ∀ n → A n → A (suc n))(n : ℕ) → A n
indℕ A z s zero = z
indℕ A z s (suc n) = s n (indℕ A z s n)

ind₂ℕ : ∀{ℓ}(A : ℕ → Set ℓ)(z : A 0)(o : A 1)(s : ∀ n → A n → A (suc (suc n)))(n : ℕ) → A n
ind₂ℕ A z o s zero = z
ind₂ℕ A z o s (suc zero) = o
ind₂ℕ A z o s (suc (suc n)) = s n (ind₂ℕ A z o s n)

ind₃ℕ : ∀{ℓ}(A : ℕ → Set ℓ)(z : A 0)(o : A 1)(t : A 2)(s : ∀ n → A n → A (suc (suc (suc n))))(n : ℕ) → A n
ind₃ℕ A z o t s zero = z
ind₃ℕ A z o t s (suc zero) = o
ind₃ℕ A z o t s (suc (suc zero)) = t
ind₃ℕ A z o t s (suc (suc (suc n))) = s n (ind₃ℕ A z o t s n)