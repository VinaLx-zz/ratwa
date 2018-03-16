open import Relation.Binary using (IsDecTotalOrder; DecTotalOrder; Rel)
open import Relation.Unary using (Decidable)

module Ratwa.List.Sort {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) hiding (_≤?_)
open IsDecTotalOrder isDecTotalOrder

-- {X : Set a}
    -- {_≈_ : Rel X ℓ₁} (_≤_ : Rel X ℓ₂)
    -- (decTotal : IsDecTotalOrder {a} {ℓ₁} {ℓ₂} {X} _≈_ _≤_)

open import Data.List using (List ; _∷_ ; [] ; partition ; _++_)
open import Data.Product using (_,_; proj₁; proj₂)

data _≤[]_ (x : X) : List X → Set _ where
    ≤[]-[] : x ≤[] []
    ≤[]-cons : ∀ {x' xs} → x ≤ x' → x ≤[] xs → x ≤[] (x' ∷ xs)

data Sorted : List X → Set _ where
    s[] : Sorted []
    _s∷_ : ∀ {x xs} → x ≤[] xs → Sorted xs → Sorted (x ∷ xs)

{-# TERMINATING #-}
quickSort : List X → List X
quickSort [] = []
quickSort (x ∷ xs) =
    let (l , r) = partition (_≤?_ x) xs
    in  quickSort l ++ x ∷ quickSort r

module Properties where

    data _[]≤_ : List X → List X → Set _ where
        []≤-[] : ∀ {xs} → [] []≤ xs
        []≤-cons : ∀ {x xs xs'} → x ≤[] xs' → xs []≤ xs' → (x ∷ xs) []≤ xs'

    quickSort-soundness : ∀ (xs : List X) → Sorted (quickSort xs)
    quickSort-soundness [] = s[]
    quickSort-soundness (x ∷ xs) = ?

