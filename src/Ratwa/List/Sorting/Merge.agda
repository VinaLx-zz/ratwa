open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sorting.Merge {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt
    renaming (Carrier to X) using ()

open import Data.List using (List)

open import Ratwa.List.Sorting.Merge.Sort (dt)
    using (mergeSort)
open import Ratwa.List.Sorting.Merge.Permutation (dt)
    using (mergeSortPermuted)
open import Ratwa.List.Sorting (dt)
open import Ratwa.List.Compare.Monotone (dt)


{-# TERMINATING #-}
mergeSortMonotone : ∀ (xs : List X) → Monotone (mergeSort xs)
mergeSortMonotone xs = ?

verifiedMergeSort : VerifiedSort
verifiedMergeSort =
    record { sort = mergeSort
           ; monotone = mergeSortMonotone
           ; permutation = mergeSortPermuted }
