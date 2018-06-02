open import Relation.Binary using (DecTotalOrder)

module Ratwa.List.Sorting.Merge.Sort {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using (_≟_; _≤?_)

open import Data.Product using (_,_; _×_)
open import Data.List using ([]; _∷_; List; splitAt; length)
open import Data.Nat using (⌊_/2⌋)
open import Relation.Nullary

merge : List X → List X → List X
merge [] ys = ys
merge xs [] = xs
merge (x ∷ xs) (y ∷ ys) with x ≟ y
... | yes x≈y = x ∷ y ∷ merge xs ys
... | no ¬x≈y with x ≤? y
...   | yes x≤y = x ∷ merge xs (y ∷ ys)
...   | no ¬x≤y = y ∷ merge (x ∷ xs) ys

halfPartition : List X → List X × List X
halfPartition xs = splitAt (⌊ length xs /2⌋) xs

{-# TERMINATING #-}
mergeSort : List X → List X
mergeSort [] = []
mergeSort xs @ (x ∷ xs′) with halfPartition xs
... | left , right = merge (mergeSort left) (mergeSort right)

