open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sorting.Quick {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X; module Eq to DE) using
    (_≈_; _≤_; _≤?_; isEquivalence)
open DE using () renaming (setoid to S)

open import Data.List using (List ; _∷_ ; [] ; partition ; _++_)
open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (refl; sym; inspect; [_])

open import Ratwa.List.Permutation.All (S)

open import Ratwa.List.Compare (dt)
open import Ratwa.List.Compare.Properties (dt)
open import Ratwa.List.Compare.Monotone (dt)
open import Ratwa.List.Sorting (dt)


{-# TERMINATING #-}
quickSort : List X → List X
quickSort [] = []
quickSort (x ∷ xs) =
    let (l , r) = partition (λ y → y ≤? x) xs
    in  quickSort l ++ x ∷ quickSort r


{-# TERMINATING #-}
quickSortPermuted : ∀ (xs : List X) → xs ↔ quickSort xs
quickSortPermuted [] = ↔-[]
quickSortPermuted (x ∷ xs)
    with partition (λ y → y ≤? x) xs | inspect (partition (λ y → y ≤? x)) xs
... | l , r | [ pe ] with quickSort l | inspect quickSort l
                        | quickSort r | inspect quickSort r
... | sl | [ refl ] | sr | [ refl ] =
    -- [ x , (sl ++ sr) ]≈ (sl ++ x ∷ sr)
    (insert x sl sr) ∷-↔ (↔-trans
        -- xs ↔ (l ++ r)
        (partition-↔-++ (sym pe))
        -- (l ++ r) ↔ (sl ++ sr)
        (↔-++ (quickSortPermuted l) (quickSortPermuted r)))

{-# TERMINATING #-}
quickSortMonotone : ∀ (xs : List X) → Monotone (quickSort xs)
quickSortMonotone [] = ↗-[]
quickSortMonotone (x ∷ xs)
    with partition (λ y → y ≤? x) xs | inspect (partition (λ y → y ≤? x)) xs
... | l , r | [ pe ] with partition-*≤≤* {xs} {x} {l} {r} (sym pe)
...     | l*≤x , x≤*r = monotone-++ (quickSortMonotone l)
            (x≤*sr ↗-∷ (quickSortMonotone r))
            (sl*≤x *≤*-∷ sl*≤x *≤≤* x≤*sr)
            where sl*≤x : quickSort l *≤ x
                  sl*≤x = *≤-↔ l*≤x (quickSortPermuted l)
                  x≤*sr : x ≤* quickSort r
                  x≤*sr = ≤*-↔ x≤*r (quickSortPermuted r)

verifiedQuickSort : VerifiedSort
verifiedQuickSort =
    record { sort = quickSort
           ; monotone = quickSortMonotone
           ; permutation = quickSortPermuted }

