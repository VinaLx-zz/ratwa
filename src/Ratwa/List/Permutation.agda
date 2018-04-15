open import Relation.Binary using (Setoid)

module Ratwa.List.Permutation {a ℓ} (S : Setoid a ℓ) where

open Setoid S using (_≈_) renaming (Carrier to X)

open import Data.List using (_∷_; []; List; partition)
open import Data.List.Relation.Pointwise using (Pointwise)

open import Ratwa.List.Permutation.Insert (S)

open import Level using (_⊔_)

-- permutation

data _↔_ : List X → List X → Set (a ⊔ ℓ) where
    perm-[] : [] ↔ []
    perm-cons : ∀ {x xs ys xs'} →
                [ x , ys ]≈ xs' → xs ↔ ys → (x ∷ xs) ↔ xs'

-- substitution (rewriting) in terms of Pointwise _≈_

↔-subst₁ : ∀ {xs ys zs} → Pointwise _≈_ xs ys → xs ↔ zs → ys ↔ zs
↔-subst₁ Pointwise.[] perm-[] = perm-[]
↔-subst₁ (x≈y Pointwise.∷ xs≈ys) (perm-cons [x,as]≈zs xs↔as) =
    perm-cons (insert-subst₁ x≈y [x,as]≈zs) (↔-subst₁ xs≈ys xs↔as)

↔-subst₂ : ∀ {xs ys zs} → Pointwise _≈_ ys zs → xs ↔ ys → xs ↔ zs
↔-subst₂ Pointwise.[] xs↔ys = xs↔ys
↔-subst₂ ys≈zs (perm-cons [x,as]≈ys xs↔as) =
    perm-cons (insert-subst₃ ys≈zs [x,as]≈ys) xs↔as

