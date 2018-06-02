open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sorting {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt
    renaming (Carrier to X; module Eq to DE) using (_≈_; _≤_)
open DE using () renaming (setoid to S)

open import Level
open import Data.List using (List ; _∷_)

open import Ratwa.List.Permutation (S)
open import Ratwa.List.Compare.Monotone (dt)

record VerifiedSort : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    sort : List X → List X
    monotone : ∀ (xs : List X) → Monotone (sort xs)
    permutation : ∀ (xs : List X) → xs ↔ sort xs

