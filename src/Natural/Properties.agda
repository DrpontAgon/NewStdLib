{-# OPTIONS --rewriting #-}

module Natural.Properties where

open import Natural.Base
open import Equality.Set
open import Prelude.Set
open import Relation.Decidable.Set
open import Relation.Reflexive.Set
open import Relation.Transitive.Set

instance
  0≠suc : {n : ℕ} → 0 ≢ℕ suc n
  0≠suc = trivial

  sucInjℕ : ∀{n m} → ⦃ i : suc n ≡ℕ suc m ⦄ → n ≡ℕ m
  sucInjℕ ⦃ i ⦄ = i

  sucInj : ∀{n m} → ⦃ i : suc n ≡ suc m ⦄ → n ≡ m
  sucInj {n} {.n} ⦃ refl ⦄ = refl

  predInjℕ : ∀{n m} → ⦃ i : n >ℕ 0 ⦄ → ⦃ j : m >ℕ 0 ⦄ → ⦃ eq : pred n ≡ℕ pred m ⦄ → n ≡ℕ m
  predInjℕ {suc n} {suc m} ⦃ eq = eq ⦄ = eq

  predInj : ∀{n m} → ⦃ i : n >ℕ 0 ⦄ → ⦃ j : m >ℕ 0 ⦄ → ⦃ eq : pred n ≡ pred m ⦄ → n ≡ m
  predInj {suc n} {suc m} ⦃ eq = eq ⦄ = cong suc eq

  sucpredℕ : ∀{n} → ⦃ i : n >ℕ 0 ⦄ → suc (pred n) ≡ℕ n
  sucpredℕ {suc zero} = trivial
  sucpredℕ {suc (suc n)} = sucpredℕ {suc n}

  sucpred : ∀{n} → ⦃ i : n >ℕ 0 ⦄ → suc (pred n) ≡ n
  sucpred {suc n} = refl

  ≢ℕ→¬≡ℕ : {n m : ℕ} → ⦃ n ≢ℕ m ⦄ → ¬ᵢ (n ≡ℕ m)
  ≢ℕ→¬≡ℕ {zero} {zero} ⦃ p ⦄ ⦃ q ⦄ = p
  ≢ℕ→¬≡ℕ {zero} {suc m} ⦃ p ⦄ ⦃ q ⦄ = q
  ≢ℕ→¬≡ℕ {suc n} {suc m} ⦃ p ⦄ ⦃ q ⦄ = ≢ℕ→¬≡ℕ {n} {m} ⦃ p ⦄ ⦃ q ⦄

  ¬≡ℕ→≢ℕ : {n m : ℕ} → ⦃ ¬ᵢ (n ≡ℕ m) ⦄ → n ≢ℕ m
  ¬≡ℕ→≢ℕ {zero} {zero} ⦃ p ⦄ = p ⦃ trivial ⦄
  ¬≡ℕ→≢ℕ {zero} {suc m} ⦃ p ⦄ = trivial
  ¬≡ℕ→≢ℕ {suc n} {zero} ⦃ p ⦄ = trivial
  ¬≡ℕ→≢ℕ {suc n} {suc m} ⦃ p ⦄ = ¬≡ℕ→≢ℕ {n} {m} ⦃ λ ⦃ i ⦄ → p ⦃ i ⦄ ⦄

  ≡ℕ→≡ : {n m : ℕ} → ⦃ n ≡ℕ m ⦄ → n ≡ m
  ≡ℕ→≡ {zero} {zero} = refl
  ≡ℕ→≡ {suc n} {suc m} ⦃ eq ⦄ = cong suc (≡ℕ→≡ {n} {m} ⦃ eq ⦄)

  ≡→≡ℕ : {n m : ℕ} → ⦃ n ≡ m ⦄ → n ≡ℕ m
  ≡→≡ℕ {n} {m} ⦃ refl ⦄ = reflℕ {n}

  Decidable≡ℕ : {x y : ℕ} → Dec (x ≡ℕ y)
  Decidable≡ℕ {zero} {zero} = yes trivial
  Decidable≡ℕ {zero} {suc y} = no id
  Decidable≡ℕ {suc x} {zero} = no id
  Decidable≡ℕ {suc x} {suc y} = Decidable≡ℕ {x} {y}

  Decidable≢ℕ : {x y : ℕ} → Dec (x ≢ℕ y)
  Decidable≢ℕ {zero} {zero} = no id
  Decidable≢ℕ {zero} {suc y} = yes trivial
  Decidable≢ℕ {suc x} {zero} = yes trivial
  Decidable≢ℕ {suc x} {suc y} = Decidable≢ℕ {x} {y}

  Decidable≡overℕ : {x y : ℕ} → Dec (x ≡ y)
  Decidable≡overℕ {zero} {zero} = yes refl
  Decidable≡overℕ {zero} {suc y} = no λ ()
  Decidable≡overℕ {suc x} {zero} = no λ ()
  Decidable≡overℕ {suc x} {suc y} with Decidable≡overℕ {x} {y}
  ...| yes p = yes (cong suc p)
  ...| no p  = no (λ eq → p (sucInj ⦃ eq ⦄))

  Decidable≤ℕ : {x y : ℕ} → Dec (x ≤ℕ y)
  Decidable≤ℕ {zero} {zero} = yes trivial
  Decidable≤ℕ {zero} {suc y} = yes trivial
  Decidable≤ℕ {suc x} {zero} = no id
  Decidable≤ℕ {suc x} {suc y} = Decidable≤ℕ {x} {y}

  Decidable<ℕ : {x y : ℕ} → Dec (x <ℕ y)
  Decidable<ℕ {zero} {zero} = no id
  Decidable<ℕ {zero} {suc y} = yes trivial
  Decidable<ℕ {suc x} {zero} = no id
  Decidable<ℕ {suc x} {suc y} = Decidable<ℕ {x} {y}

  Decidable≥ℕ : {x y : ℕ} → Dec (x ≥ℕ y)
  Decidable≥ℕ {zero} {zero} = yes trivial
  Decidable≥ℕ {zero} {suc y} = no id
  Decidable≥ℕ {suc x} {zero} = yes trivial
  Decidable≥ℕ {suc x} {suc y} = Decidable≥ℕ {x} {y}

  Decidable>ℕ : {x y : ℕ} → Dec (x >ℕ y)
  Decidable>ℕ {zero} {zero} = no id
  Decidable>ℕ {zero} {suc y} = no id
  Decidable>ℕ {suc x} {zero} = yes trivial
  Decidable>ℕ {suc x} {suc y} = Decidable>ℕ {x} {y}
  
  ≤≥≡ℕ : {n m : ℕ} → ⦃ n ≤ℕ m ⦄ → ⦃ m ≤ℕ n ⦄ → n ≡ℕ m
  ≤≥≡ℕ {zero}  {zero}  = trivial
  ≤≥≡ℕ {suc n} {suc m} = ≤≥≡ℕ {n} {m}

  n≤sucn : {n : ℕ} → n ≤ℕ suc n
  n≤sucn {zero} = trivial
  n≤sucn {suc n} = n≤sucn {n}

  <→≤ : ∀{n k} → ⦃ n <ℕ k ⦄ → n ≤ℕ k
  <→≤ {zero} {k} = trivial
  <→≤ {suc n} {suc k} ⦃ lt ⦄ = <→≤ {n} {k} ⦃ lt ⦄

  ≤→< : ∀{n k} → ⦃ n ≤ℕ k ⦄ → n <ℕ suc k
  ≤→< {n} {k} ⦃ le ⦄ = le

  >→≥ : ∀{n k} → ⦃ n >ℕ k ⦄ → n ≥ℕ k
  >→≥ {n} {zero} = trivial
  >→≥ {suc n} {suc k} ⦃ gt ⦄ = >→≥ {n} {k} ⦃ gt ⦄

  ≥→> : ∀{n k} → ⦃ n ≥ℕ k ⦄ → suc n >ℕ k
  ≥→> {n} {k} ⦃ ge ⦄ = ge

  ≡→≤ : ∀{n k} → ⦃ n ≡ℕ k ⦄ → n ≤ℕ k
  ≡→≤ {zero} {zero} = trivial
  ≡→≤ {suc n} {suc k} ⦃ eq ⦄ = ≡→≤ {n} {k} ⦃ eq ⦄

  ≡→≥ : ∀{n k} → ⦃ n ≡ℕ k ⦄ → n ≥ℕ k
  ≡→≥ {zero} {zero} = trivial
  ≡→≥ {suc n} {suc k} ⦃ eq ⦄ = ≡→≥ {n} {k} ⦃ eq ⦄

≤≥sym : {n m : ℕ} → (n ≤ℕ m) ↔ (m ≥ℕ n)
≤≥sym {n} {m} = id , id

<>sym : {n m : ℕ} → (n <ℕ m) ↔ (m >ℕ n)
<>sym {n} {m} = id , id

{-
{-
instance
  ≡ℕ≅≡ₛ : {x y : ℕ} → (x ≡ℕ y) ≅ (x ≡ₛ y)
  ≡ℕ≅≡ₛ = record 
    { left→right = ≡ℕ→≡ₛ
    ; right→left = ≡ₛ→≡ℕ
    ; →∘←≡id = funExtₛ f'
    ; ←∘→≡id = funExtₛ g' } where
    f' : {n m : ℕ}(a : n ≡ₛ m) → ≡ℕ→≡ₛ (≡ₛ→≡ℕ a) ≡ₛ a
    f' {zero} {.zero} reflₛ = reflₛ
    f' {suc n} {.(suc n)} reflₛ = congₛ (congₛ suc) (f' reflₛ)

    g' : {n m : ℕ}(a : n ≡ℕ m) → ≡ₛ→≡ℕ (≡ℕ→≡ₛ a) ≡ₛ a
    g' {.0} {.0} eqZero = reflₛ
    g' {.(suc _)} {.(suc _)} (eqSuc a) = 
      ≡ₛ→≡ℕ (congₛ suc (≡ℕ→≡ₛ a)) 
      ≡⟨ p ⟩ₛ 
      eqSuc (≡ₛ→≡ℕ (≡ℕ→≡ₛ a))
      ≡⟨ congₛ eqSuc (g' a) ⟩ₛ 
      eqSuc a
      ∎ₛ where
      p : {x y : ℕ}{n : x ≡ₛ y} → ≡ₛ→≡ℕ (congₛ suc n) ≡ₛ eqSuc (≡ₛ→≡ℕ n)
      p {x} {.x} {reflₛ} = reflₛ
-}

{-
instance
  ≤≅≥ : {n m : ℕ} → (n ≤ m) ≅ (m ≥ n)
  ≤≅≥ = record 
    { left→right = π₁ ≤≥sym
    ; right→left = π₂ ≤≥sym
    ; →∘←≡id = funExtₛ f'
    ; ←∘→≡id = funExtₛ g' } where
    f' : {n m : ℕ}(x : m ≥ n) → (π₁ ≤≥sym ∘ π₂ ≤≥sym) x ≡ₛ id x
    f' {.0} {m} ge = reflₛ
    f' {.(suc _)} {.(suc _)} (geSuc x) = congₛ geSuc (f' x)

    g' : {n m : ℕ}(x : n ≤ m) → (π₂ ≤≥sym ∘ π₁ ≤≥sym) x ≡ₛ id x
    g' {.0} {m} le = reflₛ
    g' {.(suc _)} {.(suc _)} (leSuc x) = congₛ leSuc (g' x)

  <≅> : {n m : ℕ} → (n < m) ≅ (m > n)
  <≅> = record 
    { left→right = π₁ <>sym
    ; right→left = π₂ <>sym
    ; →∘←≡id = funExtₛ f'
    ; ←∘→≡id = funExtₛ g' } where
    f' : {n m : ℕ}(x : m > n) → (π₁ <>sym ∘ π₂ <>sym) x ≡ₛ id x
    f' {.0} {m} gt = reflₛ
    f' {.(suc _)} {.(suc _)} (gtSuc x) = congₛ gtSuc (f' x)
    
    g' : {n m : ℕ}(x : n < m) → (π₂ <>sym ∘ π₁ <>sym) x ≡ₛ id x
    g' {.0} {m} lt = reflₛ
    g' {.(suc _)} {.(suc _)} (ltSuc x) = congₛ ltSuc (g' x)
-}

{-
instance
  ≤Refl : Reflexive _≤_
  ≤Refl = record { reflexive = r } where
    r : {a : ℕ} → a ≤ a
    r {zero} = le
    r {suc a} = leSuc r

  ≥Refl : Reflexive _≥_
  ≥Refl = record { reflexive = r } where
    r : {a : ℕ} → a ≥ a
    r {zero} = ge
    r {suc a} = geSuc r
  
  ≡ℕRefl : Reflexive _≡ℕ_
  ≡ℕRefl = record { reflexive = r } where
    r : {a : ℕ} → a ≡ℕ a
    r {zero} = eqZero
    r {suc a} = eqSuc r

  <Irrefl : Irreflexive _<_
  <Irrefl = record { irreflexive = r } where
    r : {a : ℕ} → ¬ (a < a)
    r (ltSuc x) = r x

  >Irrefl : Irreflexive _>_
  >Irrefl = record { irreflexive = r } where
    r : {a : ℕ} → ¬ (a > a)
    r (gtSuc x) = r x
  
  -------------------

  ≡ℕSym : Symmetric _≡ℕ_
  ≡ℕSym = record { sym = s } where
    s : {a b : ℕ} → a ≡ℕ b → b ≡ℕ a
    s eqZero = eqZero
    s (eqSuc x) = eqSuc (s x)
  
  ≤Antisym : Antisymmetric _≤_
  ≤Antisym = record { asym = asy } where
    asy : {a b : ℕ} → a ≤ b → b ≤ a → a ≡ₛ b
    asy {a} {b} x y = left→right ≡ℕ≅≡ₛ (≤≥≡ℕ x y)
  
  ≥Antisym : Antisymmetric _≥_
  ≥Antisym = record { asym = asy } where
    asy : {a b : ℕ} → a ≥ b → b ≥ a → a ≡ₛ b
    asy {a} {b} x y = left→right ≡ℕ≅≡ₛ (≤≥≡ℕ (π₂ ≤≥sym y) (π₂ ≤≥sym x))

  <StrongAntisym : StronglyAntisymmetric _<_
  <StrongAntisym = record { strong-asym = sasy } where
    sasy : {a b : ℕ} → a < b → ¬ (b < a)
    sasy (ltSuc x) (ltSuc y) = sasy x y
  
  >StrongAntisym : StronglyAntisymmetric _>_
  >StrongAntisym = record { strong-asym = sasy } where
    sasy : {a b : ℕ} → a > b → ¬ (b > a)
    sasy (gtSuc x) (gtSuc y) = sasy x y
-}
instance
  idr+ : ∀{k} → k ≡ₛ k + 0
  idr+ {zero} = reflₛ
  idr+ {suc k} = congₛ suc idr+

  sucr+ : ∀{k m} → k + suc m ≡ₛ suc (k + m)
  sucr+ {zero} {m} = reflₛ
  sucr+ {suc k} {m} = congₛ suc (sucr+ {k} {m})

  assoc+ : {x y z : ℕ} → (x + y) + z ≡ₛ x + (y + z)
  assoc+ {zero} {y} {z} = reflₛ
  assoc+ {suc x} {y} {z} = congₛ suc (assoc+ {x})

  comm+ : {x y : ℕ} → x + y ≡ₛ y + x
  comm+ {zero} {y} = idr+
  comm+ {suc x} {y} = 
    suc x + y 
    ≡⟨ sym (sucr+ {x} {y}) ⟩ₛ
    x + suc y
    ≡⟨ comm+ {x} {suc y} ⟩ₛ
    suc y + x
    ≡⟨ sym (sucr+ {y} {x}) ⟩ₛ
    y + suc x
    ∎ₛ

  idr* : ∀{k} → k ≡ₛ k * 1
  idr* {zero} = reflₛ
  idr* {suc k} = 
    suc k 
    ≡⟨ idr+ ⟩ₛ 
    suc (k + zero)
    ≡⟨ sym (sucr+ {k} {0}) ⟩ₛ 
    k + 1
    ≡⟨ congₛ (_+ 1) (idr* {k}) ⟩ₛ 
    k * 1 + 1
    ∎ₛ

  sucr* : ∀{k n} → k * suc n ≡ₛ k + k * n
  sucr* {zero} {n} = reflₛ
  sucr* {suc k} {n} = 
    suc k * suc n
    ≡⟨ reflₛ ⟩ₛ 
    k * suc n + suc n
    ≡⟨ congₛ (_+ suc n) (sucr* {k}) ⟩ₛ 
    k + k * n + suc n
    ≡⟨ assoc+ {k} ⟩ₛ 
    k + (k * n + suc n)
    ≡⟨ congₛ (k +_) (sucr+ {k * n} {n}) ⟩ₛ 
    k + suc (k * n + n)
    ≡⟨ congₛ (λ x → k + suc x) (sym (sucl* {k} {n})) ⟩ₛ 
    k + suc (suc k * n)
    ≡⟨ sucr+ {k} ⟩ₛ 
    suc k + suc k * n
    ∎ₛ

  distr*+ : {x y z : ℕ} → x * (y + z) ≡ₛ x * y + x * z
  distr*+ {zero} {y} {z} = reflₛ
  distr*+ {suc x} {y} {z} =
    suc x * (y + z) 
    ≡⟨ reflₛ ⟩ₛ
    x * (y + z) + (y + z)
    ≡⟨ congₛ (_+ (y + z)) (distr*+ {x}) ⟩ₛ
    x * y + x * z + (y + z)
    ≡⟨ congₛ (λ w → x * y + x * z + w) (comm+ {y}) ⟩ₛ
    x * y + x * z + (z + y)
    ≡⟨ assoc+ {x * y} ⟩ₛ
    x * y + (x * z + (z + y))
    ≡⟨ congₛ (λ w → x * y + w) (sym (assoc+ {x * z})) ⟩ₛ
    x * y + (x * z + z + y)
    ≡⟨ congₛ (λ w → x * y + w) (comm+ {x * z + z}) ⟩ₛ
    x * y + (y + (x * z + z))
    ≡⟨ sym (assoc+ {x * y}) ⟩ₛ
    (x * y + y) + (x * z + z)
    ≡⟨ reflₛ ⟩ₛ
    suc x * y + suc x * z
    ∎ₛ

  distr+* : {x y z : ℕ} → (x + y) * z ≡ₛ x * z + y * z
  distr+* {zero} {y} {z} = reflₛ
  distr+* {suc x} {y} {z} = 
    (suc x + y) * z 
    ≡⟨ reflₛ ⟩ₛ
    suc (x + y) * z
    ≡⟨ reflₛ ⟩ₛ
    (x + y) * z + z
    ≡⟨ congₛ (_+ z) (distr+* {x}) ⟩ₛ
    x * z + y * z + z
    ≡⟨ assoc+ {x * z} ⟩ₛ
    x * z + (y * z + z)
    ≡⟨ congₛ (x * z +_) (comm+ {y * z}) ⟩ₛ
    x * z + (z + y * z)
    ≡⟨ sym (assoc+ {x * z} {z}) ⟩ₛ
    x * z + z + y * z
    ≡⟨ reflₛ ⟩ₛ
    suc x * z + y * z
    ∎ₛ

  assoc* : {x y z : ℕ} → (x * y) * z ≡ₛ x * (y * z)
  assoc* {zero} {y} {z} = reflₛ
  assoc* {suc x} {y} {z} =
    suc x * y * z 
    ≡⟨ reflₛ ⟩ₛ
    (x * y + y) * z
    ≡⟨ distr+* {x * y} ⟩ₛ
    x * y * z + y * z
    ≡⟨ congₛ (_+ y * z) (assoc* {x}) ⟩ₛ
    x * (y * z) + y * z
    ≡⟨ sym (distr+* {x}) ⟩ₛ
    (x + 1) * (y * z)
    ≡⟨ congₛ (_* (y * z)) (comm+ {x}) ⟩ₛ
    suc x * (y * z)
    ∎ₛ

  0r* : ∀{k} → 0 ≡ₛ k * 0
  0r* {zero} = reflₛ
  0r* {suc k} = congₛ (_+ 0) (0r* {k})

  comm* : {x y : ℕ} → x * y ≡ₛ y * x
  comm* {zero} {y} = zero*β₂ {y}
  comm* {suc x} {y} = 
    suc x * y
    ≡⟨ reflₛ ⟩ₛ
    x * y + y
    ≡⟨ congₛ (_+ y) (comm* {x}) ⟩ₛ
    y * x + y
    ≡⟨ comm+ {y * x} ⟩ₛ
    y + y * x
    ≡⟨ congₛ (_+ y * x) (idr* {y}) ⟩ₛ
    y * 1 + y * x
    ≡⟨ sym (distr*+ {y} {1}) ⟩ₛ
    y * (1 + x)
    ≡⟨ reflₛ ⟩ₛ
    y * suc x
    ∎ₛ

{-
infixl 6 _-_

pred : ℕ → ℕ
pred n = π₁ (rec (0 , true) (λ {(x ,Σ y) → if y then (x ,Σ false) else (suc x ,Σ y)}) n)

_-_ : ℕ → ℕ → ℕ
x - y = rec x pred y
-}

instance
  idr- : ∀{k} → k ≡ₛ k - 0
  idr- = reflₛ

  0- : ∀{k} → 0 ≡ₛ 0 - k
  0- {zero} = reflₛ
  0- {suc k} = reflₛ

  k-k : ∀{k} → k - k ≡ₛ 0
  k-k {zero} = reflₛ
  k-k {suc k} = k-k {k}

  suc-1 : ∀{k} → suc k - 1 ≡ₛ k
  suc-1 = reflₛ

  k-1+1 : ∀{k} → {{k > 0}} → suc (k - 1) ≡ₛ k
  k-1+1 {suc zero} = reflₛ
  k-1+1 {suc (suc k)} = reflₛ

  suc< : ∀{k} → k < suc k
  suc< {zero} = lt
  suc< {suc k} = ltSuc suc<

  suc≤ : ∀{k} → k ≤ suc k
  suc≤ {zero} = le
  suc≤ {suc k} = leSuc suc≤

  suc≥ : ∀{k} → suc k ≥ k
  suc≥ {zero} = ge
  suc≥ {suc k} = geSuc suc≥

  suc> : ∀{k} → suc k > k
  suc> {zero} = gt
  suc> {suc k} = gtSuc suc>
-}

{-
instance
  maxPr : {x y : ℕ} → ((max x y ≡ℕ x) × (x ≥ℕ y)) ⊎ ((max x y ≡ℕ y) × (¬ (x ≥ y)))
  maxPr {zero} {zero} = ι₁ (eqZero ,Σ ge)
  maxPr {zero} {suc y} = ι₂ ((≡ₛ→≡ℕ reflₛ) ,Σ λ ())
  maxPr {suc x} {zero} = ι₁ ((≡ₛ→≡ℕ reflₛ) ,Σ ge)
  maxPr {suc x} {suc y} with maxPr {x} {y}
  ... | ι₁ (mx ,Σ x≥y) = ι₁ ((eqSuc mx) ,Σ (geSuc x≥y))
  ... | ι₂ (my ,Σ ¬x≥y) = ι₂ ((eqSuc my) ,Σ (λ {(geSuc f) → ¬x≥y f}))

  minPr : {x y : ℕ} → ((min x y ≡ℕ x) × (x ≤ y)) ⊎ ((min x y ≡ℕ y) × (¬ (x ≤ y)))
  minPr {zero} {zero} = ι₁ (eqZero ,Σ le)
  minPr {zero} {suc y} = ι₁ (eqZero ,Σ le)
  minPr {suc x} {zero} = ι₂ (eqZero ,Σ (λ ()))
  minPr {suc x} {suc y} with minPr {x} {y} 
  ... | ι₁ (mx ,Σ x≤y) = ι₁ (eqSuc mx ,Σ leSuc x≤y)
  ... | ι₂ (mx ,Σ ¬x≤y) = ι₂ ((eqSuc mx) ,Σ (λ {(leSuc f) → ¬x≤y f}))
-}