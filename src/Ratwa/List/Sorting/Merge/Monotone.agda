open import Relation.Binary using (DecTotalOrder)

module Ratwa.List.Sorting.Merge.Monotone {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X; module Eq to DE) using (_≟_; _≤?_; reflexive)
open DE using () renaming (sym to ≈-sym)

open import Relation.Nullary
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)

open import Ratwa.List.Sorting.Merge.Sort (dt)
open import Ratwa.List.Sorting.Merge.Permutation (dt)
open import Ratwa.List.Compare.All (dt)

merge-Monotone : ∀ {xs ys : List X} → Monotone xs → Monotone ys → Monotone (merge xs ys)
merge-Monotone ↗-[] mys = mys
merge-Monotone mxs @ (x ↗-∷ mxs') ↗-[] = mxs
merge-Monotone {x ∷ xs} {y ∷ ys} (mx ↗-∷ mxs) (my ↗-∷ mys) with x ≟ y
... | yes x≈y =
-- Monotone (x ∷ y ∷ merge xs ys)
    (reflexive x≈y ≤*-∷
        ≤*-↔ (mx ≤*-++ (≤*-subst₂ my (≈-sym x≈y))) (merge-↔ xs ys)) ↗-∷
    (≤*-↔ (≤*-subst₂ mx x≈y ≤*-++ my) (merge-↔ xs ys) ↗-∷
        merge-Monotone mxs mys)
... | no ¬x≈y with x ≤? y
...   | yes x≤y =
-- Monotone (x ∷ merge xs (y ∷ ys))
    ≤*-↔ (mx ≤*-++ (x≤y ≤*-∷ (x≤y ≤≤* my))) (merge-↔ xs (y ∷ ys)) ↗-∷
    merge-Monotone mxs (my ↗-∷ mys)
...   | no ¬x≤y with total-elim ¬x≤y
...     | y≤x =
-- Monotone (y ∷ merge (x ∷ xs) ys)
    ≤*-↔ ((y≤x ≤*-∷ y≤x ≤≤* mx) ≤*-++ my) (merge-↔ (x ∷ xs) ys) ↗-∷
    merge-Monotone (mx ↗-∷ mxs) mys

{-# TERMINATING #-}
mergeSortMonotone : ∀ (xs : List X) → Monotone (mergeSort xs)
mergeSortMonotone [] = ↗-[]
mergeSortMonotone xs @ (x ∷ xs') with halfPartition xs
... | left , right =
    merge-Monotone (mergeSortMonotone left) (mergeSortMonotone right)

