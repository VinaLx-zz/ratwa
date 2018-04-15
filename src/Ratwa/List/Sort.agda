open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sort {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using
    (_≈_; _≤_; _≤?_; isEquivalence)

open import Level
open import Data.List using (List ; _∷_ ; [] ; partition ; _++_)

private
    S : Setoid a ℓ₁
    S = record { Carrier = X; _≈_ = _≈_; isEquivalence = isEquivalence }

open import Ratwa.List.Permutation (S)
open import Ratwa.List.Permutation.Insert (S)

data _≤[]_ (x : X) : List X → Set (a ⊔ ℓ₂) where
    ≤[]-[] : x ≤[] []
    ≤[]-cons : ∀ {x' xs} → x ≤ x' → x ≤[] xs → x ≤[] (x' ∷ xs)

data Sorted : List X → Set (a ⊔ ℓ₂) where
    s[] : Sorted []
    _s∷_ : ∀ {x xs} → x ≤[] xs → Sorted xs → Sorted (x ∷ xs)

++-≤[] : ∀ {x xs ys} → x ≤[] xs → x ≤[] ys → x ≤[] (xs ++ ys)
++-≤[] ≤[]-[] x≤[]ys = x≤[]ys
++-≤[] (≤[]-cons x≤x' x≤xs) x≤[]ys = ≤[]-cons x≤x' (++-≤[] x≤xs x≤[]ys)

data _[]≤[]_ : List X → List X → Set (a ⊔ ℓ₂) where
    []≤[]-[] : ∀ {xs} → [] []≤[] xs
    []≤[]-cons : ∀ {x xs ys} → x ≤[] ys → xs []≤[] ys → (x ∷ xs) []≤[] ys

++-sorted : ∀ {xs ys} → Sorted xs → Sorted ys → xs []≤[] ys → Sorted (xs ++ ys)
++-sorted s[] ys xs[]≤[]ys = ys
++-sorted (x≤[]xs s∷ xs) ys ([]≤[]-cons x≤[]ys xs[]≤[]ys) =
    ++-≤[] x≤[]xs x≤[]ys s∷ ++-sorted xs ys xs[]≤[]ys

record IsSound (sort : List X → List X) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      permutation : ∀ (xs : List X) → xs ↔ sort xs
      sorted : ∀ (xs : List X) → Sorted (sort xs)

