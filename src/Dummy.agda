{-# OPTIONS --prop --rewriting #-}

module Dummy where

-- open import Bool
-- open import Prelude
-- open import Equality
-- open import Symmetric
{-
g : ℕ → ℕ
g x = switch (λ { 0 → true ; (suc m) → false}) cases 
        case x ⇒ 10 break
        default⇒ 0

_mod2 : ℕ → ℕ
zero mod2 = zero
suc zero mod2 = suc zero
suc (suc n) mod2 = n mod2

tr : {n : ℕ} → ((suc (n + 0)) mod2 ≡ₛ (suc (suc (suc n)) mod2)) ≡ₛ ((n + 1) mod2 ≡ₛ (n + 3) mod2)
tr {zero} = reflₛ
tr {suc zero} = reflₛ
tr {suc (suc n)} = tr {n}

biz : {n : ℕ} → {{r : n > 0}} → g n ≡ₛ g (suc n)
biz {suc n} = reflₛ

f : ℕ → ℕ
f = ?
-}