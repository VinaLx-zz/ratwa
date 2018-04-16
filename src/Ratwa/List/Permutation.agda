open import Relation.Binary using (Setoid)

module Ratwa.List.Permutation {a ℓ} (S : Setoid a ℓ) where

open Setoid S using (_≈_) renaming (Carrier to X)

open import Data.List using (_∷_; []; List; partition)
open import Data.List.Relation.Pointwise using (Pointwise)

open import Ratwa.List.Permutation.Insert (S)

open import Level using (_⊔_)

-- permutation

infix 4 _↔_

data _↔_ : List X → List X → Set (a ⊔ ℓ) where
    ↔-[] : [] ↔ []
    _∷-↔_ : ∀ {x xs ys xs'} →
                [ x , ys ]≈ xs' → xs ↔ ys → (x ∷ xs) ↔ xs'

-- substitution (rewriting) in terms of Pointwise _≈_

↔-subst₁ : ∀ {xs ys zs} → Pointwise _≈_ xs ys → xs ↔ zs → ys ↔ zs
↔-subst₁ Pointwise.[] ↔-[] = ↔-[]
↔-subst₁ (x≈y Pointwise.∷ xs≈ys) ([x,as]≈zs ∷-↔ xs↔as) =
    insert-subst₁ x≈y [x,as]≈zs ∷-↔ ↔-subst₁ xs≈ys xs↔as

↔-subst₂ : ∀ {xs ys zs} → Pointwise _≈_ ys zs → xs ↔ ys → xs ↔ zs
↔-subst₂ Pointwise.[] xs↔ys = xs↔ys
↔-subst₂ ys≈zs ([x,as]≈ys ∷-↔ xs↔as) = insert-subst₃ ys≈zs [x,as]≈ys ∷-↔ xs↔as

