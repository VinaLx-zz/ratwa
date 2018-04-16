open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sort.Quick {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using
    (_≈_; _≤_; _≤?_; isEquivalence; total)

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
open import Ratwa.List.Compare (dt)
open import Ratwa.List.Compare.Properties (dt)
open import Ratwa.List.Compare.Monotone (dt)
open import Ratwa.List.Sort (dt)


{-# TERMINATING #-}
quickSort : List X → List X
quickSort [] = []
quickSort (x ∷ xs) =
    let (l , r) = partition (λ y → y ≤? x) xs
    in  quickSort l ++ x ∷ quickSort r


{-# TERMINATING #-}
quickSort-↔ : ∀ (xs : List X) → xs ↔ quickSort xs
quickSort-↔ ([]) = perm-[]
quickSort-↔ (x ∷ xs)
    with partition (λ y → y ≤? x) xs | inspect (partition (λ y → y ≤? x)) xs
... | l , r | [ pe ] with quickSort l | inspect quickSort l
                        | quickSort r | inspect quickSort r
... | sl | [ refl ] | sr | [ refl ] =
    -- [ x , (sl ++ sr) ]≈ (sl ++ x ∷ sr)
    perm-cons (insert x sl sr) (↔-trans
            -- xs ↔ (l ++ r)
            (partition-↔-++ (sym pe))
            -- (l ++ r) ↔ (sl ++ sr)
            (↔-++ (quickSort-↔ l) (quickSort-↔ r)))

quickSort-monotone : ∀ (xs : List X) → Monotone (quickSort xs)
quickSort-monotone [] = ↗-[]
quickSort-monotone (x ∷ xs)
    with partition (λ y → y ≤? x) xs | inspect (partition (λ y → y ≤? x)) xs
... | l , r | [ pe ] with quickSort l | inspect quickSort l
                        | quickSort r | inspect quickSort r
...   | sl | [ refl ] | sr | [ refl ] = ?

soundness : VerifiedSort
soundness =
    record { sort = quickSort
           ; monotone = quickSort-monotone 
           ; permutation = quickSort-↔ }
