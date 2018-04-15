open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sort.Quick {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using
    (_≈_; _≤_; _≤?_; isEquivalence)

private
    S : Setoid a ℓ₁
    S = record { Carrier = X; _≈_ = _≈_; isEquivalence = isEquivalence }

open import Data.List using (List ; _∷_ ; [] ; partition ; _++_)
open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (refl; sym; inspect; [_])

open import Ratwa.List.Permutation (S)
open import Ratwa.List.Permutation.Insert (S)
open import Ratwa.List.Permutation.Setoid (S) using (↔-trans) 
open import Ratwa.List.Permutation.Concat (S) using (partition-↔-++; ↔-++)
open import Ratwa.List.Sort (dt)


{-# TERMINATING #-}
quickSort : List X → List X
quickSort [] = []
quickSort (x ∷ xs) =
    let (l , r) = partition (_≤?_ x) xs
    in  quickSort l ++ x ∷ quickSort r


{-# TERMINATING #-}
quickSort-↔ : ∀ (xs : List X) → xs ↔ quickSort xs
quickSort-↔ ([]) = perm-[]
quickSort-↔ (x ∷ xs) with partition (_≤?_ x) xs | inspect (partition (_≤?_ x)) xs
... | l , r | [ pe ] with quickSort l | inspect quickSort l
                        | quickSort r | inspect quickSort r
... | sl | [ refl ] | sr | [ refl ] =
    -- [ x , (sl ++ sr) ]≈ (sl ++ x ∷ sr)
    perm-cons (insert x sl sr) (↔-trans
            -- xs ↔ (l ++ r)
            (partition-↔-++ (sym pe))
            -- (l ++ r) ↔ (sl ++ sr)
            (↔-++ (quickSort-↔ l) (quickSort-↔ r)))

quickSort-sorted : ∀ (xs : List X) → Sorted (quickSort xs)
quickSort-sorted [] = s[]
quickSort-sorted (x ∷ xs) = ?

soundness : IsSound quickSort
soundness = record { permutation = quickSort-↔
                   ; sorted = quickSort-sorted }
