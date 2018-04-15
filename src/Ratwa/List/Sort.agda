open import Relation.Binary using (IsDecTotalOrder; DecTotalOrder; Rel; Setoid)
open import Relation.Unary using (Decidable)

module Ratwa.List.Sort {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using
    (_≈_; _≤_; _≤?_; isEquivalence)

open import Level

open import Data.List using (List ; _∷_ ; [] ; partition ; _++_)
open import Data.Product using (_,_; proj₁; proj₂)

private
    S : Setoid a ℓ₁
    S = record { Carrier = X; _≈_ = _≈_; isEquivalence = isEquivalence }

open import Ratwa.List.Permutation (S)
open import Ratwa.List.Permutation.Insert (S)
open import Ratwa.List.Permutation.Setoid (S) using (↔-trans) 
open import Ratwa.List.Permutation.Concat (S) using (partition-↔-++; ↔-++)

open import Relation.Binary.PropositionalEquality

data _≤[]_ (x : X) : List X → Set (a ⊔ ℓ₂) where
    ≤[]-[] : x ≤[] []
    ≤[]-cons : ∀ {x' xs} → x ≤ x' → x ≤[] xs → x ≤[] (x' ∷ xs)

data Sorted : List X → Set (a ⊔ ℓ₂) where
    s[] : Sorted []
    _s∷_ : ∀ {x xs} → x ≤[] xs → Sorted xs → Sorted (x ∷ xs)

++-≤[] : ∀ {x xs ys} → x ≤[] xs → x ≤[] ys → x ≤[] (xs ++ ys)
++-≤[] ≤[]-[] x≤[]ys = x≤[]ys
++-≤[] (≤[]-cons x≤x' x≤xs) x≤[]ys = ≤[]-cons x≤x' (++-≤[] x≤xs x≤[]ys)

{-# TERMINATING #-}
quickSort : List X → List X
quickSort [] = []
quickSort (x ∷ xs) =
    let (l , r) = partition (_≤?_ x) xs
    in  quickSort l ++ x ∷ quickSort r

data _[]≤_ : List X → List X → Set (a ⊔ ℓ₂) where
    []≤-[] : ∀ {xs} → [] []≤ xs
    []≤-cons : ∀ {x xs ys} → x ≤[] ys → xs []≤ ys → (x ∷ xs) []≤ ys

++-sorted : ∀ {xs ys} → Sorted xs → Sorted ys → xs []≤ ys → Sorted (xs ++ ys)
++-sorted s[] ys xs[]≤ys = ys
++-sorted (x≤[]xs s∷ xs) ys ([]≤-cons x≤[]ys xs[]≤ys) =
    ++-≤[] x≤[]xs x≤[]ys s∷ ++-sorted xs ys xs[]≤ys


{-# TERMINATING #-}
quickSort-↔ : ∀ {xs} → xs ↔ quickSort xs
quickSort-↔ {[]} = perm-[]
quickSort-↔ {x ∷ xs} with partition (_≤?_ x) xs | inspect (partition (_≤?_ x)) xs
... | l , r | [ pe ] with quickSort l | inspect quickSort l
                        | quickSort r | inspect quickSort r
... | sl | [ refl ] | sr | [ refl ] =
    -- [ x , (sl ++ sr) ]≈ (sl ++ x ∷ sr)
    perm-cons (insert x sl sr) (↔-trans
            -- xs ↔ (l ++ r)
            (partition-↔-++ (sym pe))
            -- (l ++ r) ↔ (sl ++ sr)
            (↔-++ {l} {r} {sl} {sr} quickSort-↔ quickSort-↔))

-- quickSort-sorted : ∀ {xs} → Sorted (quickSort xs)
-- quickSort-sorted {[]} = s[]
-- quickSort-sorted {x ∷ xs} = ?
