open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sort {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using
    (_≈_; _≤_; isEquivalence)

open import Level
open import Data.List using (List ; _∷_ ; [] ; _++_)

private
    S : Setoid a ℓ₁
    S = record { Carrier = X; _≈_ = _≈_; isEquivalence = isEquivalence }

open import Ratwa.List.Permutation (S)

infix 4 _≤*_ _*≤*_
infix 3 _≤*-∷_ _*≤*-∷_ _↗-∷_

data _≤*_ (x : X) : List X → Set (a ⊔ ℓ₂) where
    ≤*-[] : x ≤* []
    _≤*-∷_ : ∀ {x' xs} → x ≤ x' → x ≤* xs → x ≤* (x' ∷ xs)

data _*≤*_ : List X → List X → Set (a ⊔ ℓ₂) where
    *≤*-[] : ∀ {xs} → [] *≤* xs
    _*≤*-∷_ : ∀ {x xs ys} → x ≤* ys → xs *≤* ys → (x ∷ xs) *≤* ys

data Monotone : List X → Set (a ⊔ ℓ₂) where
    ↗-[] : Monotone []
    _↗-∷_ : ∀ {x xs} → x ≤* xs → Monotone xs → Monotone (x ∷ xs)

infix 4 _≤*-++_
_≤*-++_ : ∀ {x xs ys} → x ≤* xs → x ≤* ys → x ≤* (xs ++ ys)
_≤*-++_ ≤*-[] x≤*ys = x≤*ys
_≤*-++_ (x≤x' ≤*-∷ x≤*xs) x≤*ys = x≤x' ≤*-∷ x≤*xs ≤*-++ x≤*ys

monotone-++ : ∀ {xs ys} → Monotone xs → Monotone ys
              → xs *≤* ys → Monotone (xs ++ ys)
monotone-++ ↗-[] ys xs*≤*ys = ys
monotone-++ (x≤*xs ↗-∷ xs) ys (x≤*ys *≤*-∷ xs*≤*ys) =
    x≤*xs ≤*-++ x≤*ys ↗-∷ monotone-++ xs ys xs*≤*ys

record VerifiedSort : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    sort : List X → List X
    monotone : ∀ (xs : List X) → Monotone (sort xs)
    permutation : ∀ (xs : List X) → xs ↔ sort xs

