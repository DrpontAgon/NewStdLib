{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Either
open import FunctorApplicativeSelectiveMonad

module List where

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 5 _::_
infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

idr[]++ : {A : Set}{xs : List A} → xs ++ [] ≡ xs
idr[]++ {A} {[]} = refl
idr[]++ {A} {x :: xs} = cong (x ::_) (idr[]++ {A} {xs})

assoc++ : {A : Set}{a b c : List A} → (a ++ b) ++ c ≡ a ++ b ++ c
assoc++ {A} {[]} {b} {c} = refl
assoc++ {A} {a :: ax} {b} {c} = cong (a ::_) (assoc++ {A} {ax})

intersperse : {A : Set} → (a : A) → List A → List A
intersperse a [] = []
intersperse a (x :: []) = x :: []
intersperse a (x :: y :: xs) = x :: a :: intersperse a (y :: xs)

instance
  FunctorList : Functor List
  FunctorList = record 
    { fmap = map
    ; idF = mapId
    ; ∘F = compF } where
      map : {A B : Set} → (A → B) → List A → List B
      map f [] = []
      map f (x :: xs) = f x :: map f xs

      mapId2 : {A : Set} → ((xs : List A) → map id xs ≡ xs)
      mapId2 [] = refl
      mapId2 (x :: xs) = cong (x ::_) (mapId2 xs)

      mapId : {A : Set} → map {A} {A} id ≡ id
      mapId = funExt λ {[] → refl
                      ; (x :: xs) → cong (x ::_) (mapId2 xs)}

      compF2 : {A B C : Set}{f : B → C}{g : A → B}(xs : List A) → (map f ∘ map g) xs ≡ map (f ∘ g) xs
      compF2 [] = refl
      compF2 {A} {B} {C} {f} {g} (x :: xs) = cong (f (g x) ::_) (compF2 xs)

      compF : {A B C : Set}{f : B → C}{g : A → B} → map f ∘ map g ≡ map (f ∘ g)
      compF {f = f} {g = g} = funExt λ {[] → refl
                                      ; (x :: xs) → cong (f (g x) ::_ ) (compF2 xs)}

  ApplicativeList : Applicative List
  ApplicativeList = record
    { pure = _:: []
    ; _⊛_ = ap
    ; functorF = FunctorList
    ; idA = idA1
    ; ∘A = λ {A} {B} {C} {a} {b} {c} → compA {c = c}
    ; homoA = refl
    ; interchangeA = λ {A} {B} {f} {x} → fmap (λ z → z x) f ++ []
          ≡⟨ idr[]++ ⟩ 
        fmap (λ z → z x) f
          ≡⟨ apFmap2 ⟩
        ap ((λ g → g x) :: []) f
        ∎ } where
      ap : {A B : Set} → List (A → B) → List A → List B
      ap fs (x :: xs) = fmap (λ g → g x) fs ++ ap fs xs
      ap _  []        = []

      idA1 : {A : Set}{xs : List A} → ap (id :: []) xs ≡ xs
      idA1 {A} {[]} = refl
      idA1 {A} {x :: xs} = cong (x ::_) (idA1 {A} {xs})

      apFmap1 : {A B : Set}{x : A}{fs : List (A → B)} → fmap (λ g → g x) fs ≡ ap fs (x :: [])
      apFmap1 = sym (idr[]++)

      apFmap2 : {A B : Set}{x : A}{fs : List (A → B)} → fmap (λ g → g x) fs ≡ ap ((λ g → g x) :: []) fs
      apFmap2 {x = x} {fs = []} = refl
      apFmap2 {x = x} {fs = f :: fs} = cong (f x ::_) (apFmap2 {x = x} {fs = fs})

      apFmap3 : {A B : Set}{xs : List A}{f : A → B} → fmap f xs ≡ ap (f :: []) xs
      apFmap3 {xs = []} {f = f} = refl
      apFmap3 {xs = x :: xs} {f = f} = cong (f x ::_) apFmap3

      fmap++ : {A B : Set}{f : A → B}{xs : List A}{ys : List A} → fmap f (xs ++ ys) ≡ fmap f xs ++ fmap f ys
      fmap++ {A} {B} {f} {[]} {ys} = refl
      fmap++ {A} {B} {f} {x :: xs} {ys} = cong (f x ::_) (fmap++ {xs = xs})

      ap∘Fmap : {A B C : Set}{a : List (B → C)}{b : List (A → B)}{c : A} → fmap (λ z → z c) (ap (fmap _∘_ a) b) ≡ ap a (fmap (λ z → z c) b)
      ap∘Fmap {A} {B} {C} {a} {[]} {c} = refl
      ap∘Fmap {A} {B} {C} {a} {b :: bs} {c} = 
        fmap (λ z → z c) (fmap (λ z → z b) (fmap _∘_ a) ++ ap (fmap _∘_ a) bs)
          ≡⟨ fmap++ {xs = (fmap (λ z → z b) (fmap _∘_ a))} ⟩
        fmap (λ z → z c) (fmap (λ z → z b) (fmap _∘_ a)) ++ fmap (λ z → z c) (ap (fmap _∘_ a) bs)
          ≡⟨ cong (_++ fmap (λ z → z c) (ap (fmap _∘_ a) bs)) (cong (λ y → y (fmap _∘_ a)) ∘F) ⟩
        fmap ((λ z → z c) ∘ (λ z → z b)) (fmap _∘_ a) ++ fmap (λ z → z c) (ap (fmap _∘_ a) bs)
          ≡⟨ cong (_++ fmap (λ z → z c) (ap (fmap _∘_ a) bs)) (cong (λ y → y a) ∘F) ⟩
        fmap (((λ z → z c) ∘ (λ z → z b)) ∘ _∘_) a ++ fmap (λ z → z c) (ap (fmap _∘_ a) bs)
          ≡⟨ refl ⟩
        fmap (λ z → z (b c)) a ++ fmap (λ z → z c) (ap (fmap _∘_ a) bs)
          ≡⟨ cong (fmap (λ z → z (b c)) a ++_) (ap∘Fmap {b = bs}) ⟩
        fmap (λ z → z (b c)) a ++ ap a (fmap (λ z → z c) bs)
        ∎

      ap++ : {A B : Set}{a : List (A → B)}{b c : List A} → ap a (b ++ c) ≡ ap a b ++ ap a c
      ap++ {A} {B} {a} {[]} {c} = refl
      ap++ {A} {B} {a} {b :: bs} {c} = 
        fmap (λ z → z b) a ++ ap a (bs ++ c)
          ≡⟨ cong (fmap (λ z → z b) a ++_) (ap++ {b = bs}) ⟩
        fmap (λ z → z b) a ++ ap a bs ++ ap a c
          ≡⟨ sym (assoc++ {a = fmap (λ z → z b) a}) ⟩
        (fmap (λ z → z b) a ++ ap a bs) ++ ap a c
        ∎

      ≡++ : {A : Set}{a b c d : List A} → a ≡ b → c ≡ d → a ++ c ≡ b ++ d
      ≡++ refl refl = refl

      compA : {A B C : Set}{a : List (B → C)}{b : List (A → B)}{c : List A} → ap (ap (ap (_∘_ :: []) a) b) c ≡ ap a (ap b c)
      compA {A} {B} {C} {a} {b} {[]} = refl
      compA {A} {B} {C} {a} {b} {c :: cs} = 
        fmap (λ z → z c) (ap (ap (_∘_ :: []) a) b) ++ ap (ap (ap (_∘_ :: []) a) b) cs
          ≡⟨ cong (λ x → fmap (λ z → z c) (ap x b) ++ ap (ap (ap (_∘_ :: []) a) b) cs) (sym apFmap3) ⟩
        fmap (λ z → z c) (ap (fmap _∘_ a) b) ++ ap (ap (ap (_∘_ :: []) a) b) cs
          ≡⟨ cong (_++ ap (ap (ap (_∘_ :: []) a) b) cs) (ap∘Fmap {b = b}) ⟩
        ap a (fmap (λ z → z c) b) ++ ap (ap (ap (_∘_ :: []) a) b) cs
          ≡⟨ cong (ap a (fmap (λ z → z c) b) ++_) (compA {c = cs}) ⟩
        ap a (fmap (λ z → z c) b) ++ ap a (ap b cs)
          ≡⟨ sym (ap++ {b = fmap (λ z → z c) b}) ⟩
        ap a (fmap (λ z → z c) b ++ ap b cs)
        ∎

idA1 : {A : Set}{xs : List A} → (_⊛_) (id :: []) xs ≡ xs
idA1 {A} {[]} = refl
idA1 {A} {x :: xs} = cong (x ::_) (idA1 {A} {xs})

apFmap1 : {A B : Set}{x : A}{fs : List (A → B)} → fmap (λ g → g x) fs ≡ (_⊛_) fs (x :: [])
apFmap1 = sym (idr[]++)

apFmap2 : {A B : Set}{x : A}{fs : List (A → B)} → fmap (λ g → g x) fs ≡ (_⊛_) ((λ g → g x) :: []) fs
apFmap2 {x = x} {fs = []} = refl
apFmap2 {x = x} {fs = f :: fs} = cong (f x ::_) (apFmap2 {x = x} {fs = fs})

apFmap3 : {A B : Set}{xs : List A}{f : A → B} → fmap f xs ≡ (_⊛_) (f :: []) xs
apFmap3 {xs = []} {f = f} = refl
apFmap3 {xs = x :: xs} {f = f} = cong (f x ::_) apFmap3

fmap++ : {A B : Set}{f : A → B}{xs : List A}{ys : List A} → fmap f (xs ++ ys) ≡ fmap f xs ++ fmap f ys
fmap++ {A} {B} {f} {[]} {ys} = refl
fmap++ {A} {B} {f} {x :: xs} {ys} = cong (f x ::_) (fmap++ {xs = xs})

ap∘Fmap : {A B C : Set}{a : List (B → C)}{b : List (A → B)}{c : A} → fmap (λ z → z c) ((_⊛_) (fmap _∘_ a) b) ≡ (_⊛_) a (fmap (λ z → z c) b)
ap∘Fmap {A} {B} {C} {a} {[]} {c} = refl
ap∘Fmap {A} {B} {C} {a} {b :: bs} {c} = 
  fmap (λ z → z c) (fmap  (λ z → z b) (fmap _∘_ a) ++ (_⊛_) (fmap  _∘_ a) bs)
    ≡⟨ fmap++ {xs = (fmap  (λ z → z b) (fmap  _∘_ a))} ⟩
  fmap (λ z → z c) (fmap  (λ z → z b) (fmap  _∘_ a)) ++ fmap (λ z → z c) ((_⊛_) (fmap  _∘_ a) bs)
    ≡⟨ cong (_++ fmap (λ z → z c) ((_⊛_) (fmap  _∘_ a) bs)) (cong (λ y → y (fmap _∘_ a)) (∘F {{FunctorList}})) ⟩
  fmap ((λ z → z c) ∘ (λ z → z b)) (fmap  _∘_ a) ++ fmap (λ z → z c) ((_⊛_) (fmap  _∘_ a) bs)
    ≡⟨ cong (_++ fmap (λ z → z c) ((_⊛_) (fmap  _∘_ a) bs)) (cong (λ y → y a) (∘F {{FunctorList}})) ⟩
  fmap (((λ z → z c) ∘ (λ z → z b)) ∘ _∘_) a ++ fmap (λ z → z c) ((_⊛_) (fmap _∘_ a) bs)
    ≡⟨ refl ⟩
  fmap (λ z → z (b c)) a ++ fmap (λ z → z c) ((_⊛_) (fmap  _∘_ a) bs)
    ≡⟨ cong (fmap (λ z → z (b c)) a ++_) (ap∘Fmap {b = bs}) ⟩
  fmap (λ z → z (b c)) a ++ (_⊛_) a (fmap (λ z → z c) bs)
  ∎

ap++ : {A B : Set}{a : List (A → B)}{b c : List A} → (_⊛_) a (b ++ c) ≡ (_⊛_) a b ++ (_⊛_) a c
ap++ {A} {B} {a} {[]} {c} = refl
ap++ {A} {B} {a} {b :: bs} {c} = 
  fmap (λ z → z b) a ++ (_⊛_) a (bs ++ c)
    ≡⟨ cong (fmap (λ z → z b) a ++_) (ap++ {b = bs}) ⟩
  fmap (λ z → z b) a ++ (_⊛_) a bs ++ (_⊛_) a c
    ≡⟨ sym (assoc++ {a = fmap (λ z → z b) a}) ⟩
  (fmap (λ z → z b) a ++ (_⊛_) a bs) ++ (_⊛_) a c
  ∎

≡++ : {A : Set}{a b c d : List A} → a ≡ c → b ≡ d → a ++ b ≡ c ++ d
≡++ refl refl = refl

compA : {A B C : Set}{a : List (B → C)}{b : List (A → B)}{c : List A} → (_⊛_) ((_⊛_) ((_⊛_) (_∘_ :: []) a) b) c ≡ (_⊛_) a ((_⊛_) b c)
compA {A} {B} {C} {a} {b} {[]} = refl
compA {A} {B} {C} {a} {b} {c :: cs} = 
  fmap (λ z → z c) ((_⊛_) ((_⊛_) (_∘_ :: []) a) b) ++ (_⊛_) ((_⊛_) ((_⊛_) (_∘_ :: []) a) b) cs
    ≡⟨ cong (λ x → fmap (λ z → z c) ((_⊛_) x b) ++ (_⊛_) ((_⊛_) ((_⊛_) (_∘_ :: []) a) b) cs) (sym apFmap3) ⟩
  fmap (λ z → z c) ((_⊛_) (fmap _∘_ a) b) ++ (_⊛_) ((_⊛_) ((_⊛_) (_∘_ :: []) a) b) cs
    ≡⟨ cong (_++ (_⊛_) ((_⊛_) ((_⊛_) (_∘_ :: []) a) b) cs) (ap∘Fmap {b = b}) ⟩
  (_⊛_) a (fmap (λ z → z c) b) ++ (_⊛_) ((_⊛_) ((_⊛_) (_∘_ :: []) a) b) cs
    ≡⟨ cong ((_⊛_) a (fmap (λ z → z c) b) ++_) (compA {c = cs}) ⟩
  (_⊛_) a (fmap (λ z → z c) b) ++ (_⊛_) a ((_⊛_) b cs)
    ≡⟨ sym (ap++ {b = fmap (λ z → z c) b}) ⟩
  (_⊛_) a (fmap (λ z → z c) b ++ (_⊛_) b cs)
  ∎
{-
instance
  SelectiveList : Selective List
  SelectiveList = record
    { select = s
    ; applicativeS = ApplicativeList
    ; idS = idS'
    ; distr*>S = {!   !}
    ; assocS = {!   !} } where
      s : {A B : Set}(xs : List (A ⊎ B))(f : List (A → B)) → List B
      s [] f = []
      s (ι₁ x :: xs) f = fmap (λ g → g x) f ++ s xs f
      s (ι₂ x :: xs) f = x :: s xs f
  
      idS' : {A : Set}{x : List (A ⊎ A)} → s x (pure id) ≡ fmap (λ y → case y id id) x
      idS' {A} {[]} = refl
      idS' {A} {ι₁ x :: xs} = cong (x ::_) idS'
      idS' {A} {ι₂ x :: xs} = cong (x ::_) idS'
  
      ap[]l : {A B : Set}{x : List A} → ((_⊛_) [] x) ≡ (the (List B) [])
      ap[]l {A} {B} {[]} = refl
      ap[]l {A} {B} {x :: xs} = ap[]l {A} {B} {xs}
  
      compApp : {A B : Set}{f : A → B}{x : A} → 
        (_∘_) {A = A → B} (λ g → g x) ((λ g → g f) ∘ const id) ≡ (λ g → g (f x)) ∘ ((_∘_) {B = B} (const id) (λ g → g x))
      compApp = refl
  
      distr*>S' : {A B : Set} {x : A ⊎ B} {y z : List (A → B)} → 
        s (pure x) ((_*>_) y z) ≡ (_*>_) (s (pure x) y) (s (pure x) z)
      distr*>S' {A} {B} {ι₁ x} {[]} {z} = 
        fmap (λ f → f x) ((_⊛_) [] z) ++ [] 
          ≡⟨ idr[]++ ⟩
        fmap (λ f → f x) ((_⊛_) [] z)
          ≡⟨ cong (fmap (λ f → f x)) (ap[]l {A → B} {A → B} {z}) ⟩
        []
          ≡⟨ sym (ap[]l {_} {_} {fmap (λ f → f x) z ++ []}) ⟩
        (_⊛_) [] (fmap (λ f → f x) z ++ [])
        ∎
      distr*>S' {A} {B} {ι₁ x} {y :: ys} {[]} = refl
      distr*>S' {A} {B} {ι₁ x} {y :: ys} {z :: zs} = 
        z x :: fmap (λ f → f x) (fmap (λ f → f z) (fmap (λ _ x → x) ys) ++ (_⊛_) (id :: fmap (λ _ x → x) ys) zs) ++ [] 
          ≡⟨ idr[]++ ⟩
        z x :: fmap (λ f → f x) (fmap (λ f → f z) (fmap (λ _ x → x) ys) ++  (_⊛_) ((λ x → x) :: fmap (λ _ x → x) ys) zs)
          ≡⟨ cong (z x ::_) ((fmap++ {_} {_} {_} 
            {fmap (λ f → f z) (fmap (const id) ys)} 
            {(_⊛_) (id :: fmap (const id) ys) zs})) ⟩
        z x :: fmap (λ z → z x) (fmap (λ f → f z) (fmap (λ _ x → x) ys)) ++ fmap (λ f → f x) ((_⊛_) (id :: fmap (λ _ x →  x) ys) zs)
          ≡⟨ cong (z x ::_) (≡++ {B} {fmap (λ f → f x) (fmap (λ f → f z) (fmap (λ _ x₁ → x₁) ys))} {fmap (λ f → f x) (( (_⊛_) (id :: fmap (λ _ x₁ → x₁) ys)) zs)} {fmap (λ g → g (z x)) (fmap (const id) (fmap (λ g → g x) ys ++ []))} { (_⊛_) (const id (y x) :: fmap (const id) (fmap (λ g → g x) ys ++ [])) (fmap (λ g → g x) zs ++ [])} (fmap (λ f →  f x) (fmap (λ f → f z) (fmap (λ _ x₁ → x₁) ys))
          ≡⟨ {! ∘F  !} ⟩
          {! fmap ((λ f → f x) ∘ (λ f → f z)) (fmap (λ _ x₁ → x₁) ys)  !}
          ≡⟨ {!   !} ⟩
          {!   !}
          ∎) {!   !}) ⟩ -- (≡++ {!   !} {!   !})
        {!   !}
        ∎  
      distr*>S' {A} {B} {ι₂ x} {y} {z} = refl -}
    {-
    fmap (λ z → z x) ((_⊛_) (id :: fmap (λ _ x → x) ys) zs) ++ []
        ≡⟨ idr[]++ ⟩
      fmap (λ z → z x) ((_⊛_) (id :: fmap (λ _ x → x) ys) zs)
        ≡⟨ {!   !} ⟩
      {!   !}
        ≡⟨ {!   !} ⟩
      (_⊛_) (id :: fmap (λ _ x → x) (fmap (λ z → z x) ys ++ [])) (fmap (λ z → z x) zs ++ [])
      ∎
    -}
{-ℕ
branch SelectiveList ((ι₁ 0) :: (ι₂ (the ℕ 5)) :: (ι₁ (the ℕ 10)) :: []) ((the (ℕ -> ℕ) suc) :: (\x -> suc (suc x)) :: []) (the (ℕ -> ℕ) (\x -> suc (suc (suc x))) :: [])
branch : {A B C : Set}(ab : S (A ⊎ B)) → S (A → C) → S (B → C) → S C
MonadList : Monad List
MonadList = record
  { bind = bindH
  ; applicativeM = ApplicativeList
  ; idlM = λ {A} {B} {f} {x} → idlM' {A} {B} {f} {x}
  ; idrM = idrM'
  ; assocM = λ {A} {B} {C} {f} {g} {h} → assocM' {A} {B} {C} {f} {g} {h}} where
    bindH : {A B : Set}(xs : List A)(f : A → List B) → List B
    bindH [] f = []
    bindH (x :: xs) f = f x ++ bindH xs f
    
    idlM' : {A B : Set}{f : A → List B}{x : A} → (bindH (pure ApplicativeList x) f) ≡ f x
    idlM' = idr[]++

    idrM' : {A : Set}{xs : List A} → (bindH xs (pure ApplicativeList)) ≡ xs
    idrM' {A} {[]} = refl
    idrM' {A} {x :: xs} = cong (x ::_) idrM'

    bind++ : {A B : Set}{ys zs : List A}{f : A → List B} → bindH (ys ++ zs) f ≡ bindH ys f ++ bindH zs f
    bind++ {ys = []} = refl
    bind++ {ys = y :: ys} {zs = zs} {f = f} = 
      f y ++ bindH (ys ++ zs) f
        ≡⟨ cong (f y ++_) (bind++ {ys = ys} {zs = zs}) ⟩
      f y ++ bindH ys f ++ bindH zs f
        ≡⟨ sym (assoc++ {a = f y}) ⟩
      (f y ++ bindH ys f) ++ bindH zs f
      ∎
    
    assocM' : {A B C : Set}{xs : List A}{f : A → List B}{g : B → List C} → (bindH (bindH xs f) g) ≡ (bindH xs (λ x → bindH (f x) g))
    assocM' {xs = []} {f = f} {g = g} = refl
    assocM' {xs = x :: xs} {f = f} {g = g} = 
      bindH (f x ++ bindH xs f) g
        ≡⟨ bind++ {ys = f x} ⟩
      bindH (f x) g ++ bindH (bindH xs f) g
        ≡⟨ cong (bindH (f x) g ++_) (assocM' {xs = xs}) ⟩
      bindH (f x) g ++ bindH xs (λ z → bindH (f z) g)
      ∎
-}
{-
MonadList : Monad List
bind MonadList [] f = []
bind MonadList (x :: xs) f = f x ++ bind MonadList xs f
applicativeM MonadList = ApplicativeList
idlM MonadList = idr[]++
idrM MonadList {A} {[]} = refl
idrM MonadList {A} {x :: xs} = cong (x ::_) (idrM MonadList)
assocM MonadList {A} {B} {C} {[]} {g} {h} = refl
assocM MonadList {A} {B} {C} {x :: xs} {g} {h} = 
  bind MonadList (g x ++ bind MonadList xs g) h 
    ≡⟨ bind++ (g x) (bind MonadList xs g) ⟩
  bind MonadList (g x) h ++ bind MonadList (bind MonadList xs g) h
    ≡⟨ cong (bind MonadList (g x) h ++_) (assocM MonadList {A} {B} {C} {xs} {g} {h}) ⟩
  bind MonadList (g x) h ++ bind MonadList xs (λ y → bind MonadList (g y) h) 
  ∎ 
    where
      bind++ : {A B : Set}(ys zs : List A){f : A → List B} → bind MonadList (ys ++ zs) f ≡ bind MonadList ys f ++ bind  MonadList zs f
      bind++ [] _ {f = f} = refl
      bind++ (y :: ys) zs {f = f} = 
        f y ++ bind MonadList (ys ++ zs) f
          ≡⟨ cong (f y ++_) (bind++ ys zs) ⟩
        f y ++ bind MonadList ys f ++ bind MonadList zs f
          ≡⟨ sym (assoc++ {a = f y}) ⟩
        (f y ++ bind MonadList ys f) ++ bind MonadList zs f
        ∎
-}