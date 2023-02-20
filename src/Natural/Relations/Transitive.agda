{-# OPTIONS --safe #-}

module Natural.Relations.Transitive where

open import Natural.Base
open import Prelude.Set using (trivial)
open import Relation.Transitive.Set

instance
  ≡ℕTrans : Transitive _≡ℕ_
  ≡ℕTrans = record { trans = λ where {x} → proof {x} } where
    proof : {x y z : ℕ} → x ≡ℕ y → y ≡ℕ z → x ≡ℕ z
    proof {zero} {zero} {zero} eq1 eq2 = trivial
    proof {suc x} {suc y} {suc z} eq1 eq2 = proof {x} eq1 eq2

  ≤ℕTrans : Transitive _≤ℕ_
  ≤ℕTrans = record { trans = λ where {x} → proof {x} } where
    proof : {x y z : ℕ} → x ≤ℕ y → y ≤ℕ z → x ≤ℕ z
    proof {zero} {y} {z} eq1 eq2 = trivial
    proof {suc x} {suc y} {suc z} eq1 eq2 = proof {x} eq1 eq2

  <ℕTrans : Transitive _<ℕ_
  <ℕTrans = record { trans = λ where {x} {y} {z} → proof {x} {y} {z} } where
    proof : {x y z : ℕ} → x <ℕ y → y <ℕ z → x <ℕ z
    proof {zero} {suc y} {suc (suc z)} eq1 eq2 = trivial
    proof {suc x} {suc (suc y)} {suc (suc (suc z))} eq1 eq2 = proof {x} {suc y} {suc (suc z)} eq1 eq2

  ≥ℕTrans : Transitive _≥ℕ_
  ≥ℕTrans = record { trans = λ where {x} {y} {z} → proof {x} {y} {z} } where
    proof : {x y z : ℕ} → x ≥ℕ y → y ≥ℕ z → x ≥ℕ z
    proof {x} {y} {zero} eq1 eq2 = trivial
    proof {suc x} {suc y} {suc z} eq1 eq2 = proof {x} {y} {z} eq1 eq2

  >ℕTrans : Transitive _>ℕ_
  >ℕTrans = record { trans = λ where {x} → proof {x} } where
    proof : {x y z : ℕ} → x >ℕ y → y >ℕ z → x >ℕ z
    proof {suc x} {suc y} {zero} eq1 eq2 = trivial
    proof {suc x} {suc y} {suc z} eq1 eq2 = proof {x} eq1 eq2

infixr 2 _≡→≤⟨_⟩_ _≡→≥⟨_⟩_ _≤ℕ⟨_⟩_ _<ℕ⟨_⟩_ _>ℕ⟨_⟩_ _≥ℕ⟨_⟩_ _≡ℕ⟨_⟩_

_≡→≤⟨_⟩_ : (x : ℕ) → {y z : ℕ} → x ≡ℕ y → y ≤ℕ z → x ≤ℕ z
zero ≡→≤⟨ eq ⟩ le = trivial
_≡→≤⟨_⟩_ (suc x) {suc y} {suc z} eq le = x ≡→≤⟨ eq ⟩ le

_≡→≥⟨_⟩_ : (x : ℕ) → {y z : ℕ} → x ≡ℕ y → y ≥ℕ z → x ≥ℕ z
_≡→≥⟨_⟩_ x {y} {zero} eq ge = trivial
_≡→≥⟨_⟩_ (suc x) {suc y} {suc z} eq ge = _≡→≥⟨_⟩_ x {y} {z} eq ge

_≤ℕ⟨_⟩_ : (x : ℕ) → {y z : ℕ} → x ≤ℕ y → y ≤ℕ z → x ≤ℕ z
_≤ℕ⟨_⟩_ x = trans {R = _≤ℕ_} {x = x}

_<ℕ⟨_⟩_ : (x : ℕ) → {y z : ℕ} → x <ℕ y → y <ℕ z → x <ℕ z
_<ℕ⟨_⟩_ x {y} {z} = trans {R = _<ℕ_} {z = z}

_>ℕ⟨_⟩_ : (x : ℕ) → {y z : ℕ} → x >ℕ y → y >ℕ z → x >ℕ z
_>ℕ⟨_⟩_ x = trans {R = _>ℕ_} {x = x}

_≥ℕ⟨_⟩_ : (x : ℕ) → {y z : ℕ} → x ≥ℕ y → y ≥ℕ z → x ≥ℕ z
_≥ℕ⟨_⟩_ x {y} {z} = trans {R = _≥ℕ_} {z = z}

_≡ℕ⟨_⟩_ : (x : ℕ) → {y z : ℕ} → x ≡ℕ y → y ≡ℕ z → x ≡ℕ z
_≡ℕ⟨_⟩_ x = trans {R = _≡ℕ_} {x = x}
