open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sort.Merge {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using
    (_≈_; _≤_; _≤?_; isEquivalence; total)

private
    S : Setoid a ℓ₁
    S = record { Carrier = X; _≈_ = _≈_; isEquivalence = isEquivalence }

open import Data.List using (List ; _∷_ ; []; splitAt; length)
open import Data.Product using (_,_)
open import Data.Nat using (⌊_/2⌋)
open import Relation.Nullary using (Dec; yes; no)

open import Ratwa.List.Permutation (S)
open import Ratwa.List.Compare.Monotone (dt)
open import Ratwa.List.Sort (dt)


merge : List X → List X → List X
merge [] ys = ys
merge xs [] = xs
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes x≤y = x ∷ merge xs (y ∷ ys)
... | no ¬x≤y = y ∷ merge (x ∷ xs) ys


{-# TERMINATING #-}
mergeSort : List X → List X
mergeSort [] = []
mergeSort xs @ (x ∷ xs′) with splitAt (⌊ length xs /2⌋) xs
... | left , right = merge (mergeSort left) (mergeSort right)

{-# TERMINATING #-}
mergeSortPermuted : ∀ (xs : List X) → xs ↔ mergeSort xs
mergeSortPermuted xs = ?

{-# TERMINATING #-}
mergeSortMonotone : ∀ (xs : List X) → Monotone (mergeSort xs)
mergeSortMonotone xs = ?

verifiedQuickSort : VerifiedSort
verifiedQuickSort =
    record { sort = mergeSort
           ; monotone = mergeSortMonotone
           ; permutation = mergeSortPermuted }
