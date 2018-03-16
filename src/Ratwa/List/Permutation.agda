open import Relation.Binary using (DecSetoid; IsDecEquivalence)

module Ratwa.List.Permutation {a ℓ} (DS : DecSetoid a ℓ) where

open DecSetoid DS renaming (Carrier to X) hiding (_≟_)
open IsDecEquivalence isDecEquivalence

open import Level

open import Data.List using (_∷_; []; List)
open import Data.List.Relation.Pointwise using (Pointwise)

open import Data.List.Relation.Equality.Setoid (DecSetoid.setoid DS)

data [_,_]≈_ : X → List X → List X → Set ℓ where
    justCons : ∀ {x y xs ys} → x ≈ y →
               Pointwise _≈_ xs ys → [ x , xs ]≈ (y ∷ ys)
    later : ∀ {x y z xs xs'} → y ≈ z → 
            [ x , xs ]≈ xs' → [ x , y ∷ xs ]≈ (z ∷ xs')

insert-subst : ∀ {x y xs xs'} → [ x , xs ]≈ xs' → y ≈ x → [ y , xs ]≈ xs'
insert-subst (justCons x≈z xs≈zs) y≈x =
    justCons (DecSetoid.trans DS y≈x x≈z) xs≈zs
insert-subst (later z≈z' [x,xs]≈xs') y≈x =
    later z≈z' (insert-subst [x,xs]≈xs' y≈x)

-- Permutation

data _↔_ : List X → List X → Set (a ⊔ ℓ) where
    perm-[] : [] ↔ []
    perm-cons : ∀ {x xs ys xs'} →
                [ x , ys ]≈ xs' → xs ↔ ys → (x ∷ xs) ↔ xs'

↔-subst : ∀ {xs ys zs} → Pointwise _≈_ xs ys → xs ↔ zs → ys ↔ zs
↔-subst Pointwise.[] perm-[] = perm-[]
↔-subst (x≈y Pointwise.∷ xs≈ys) (perm-cons [x,as]≈zs xs↔as) =
    perm-cons (insert-subst [x,as]≈zs (DecSetoid.sym DS x≈y))
              (↔-subst xs≈ys xs↔as)

↔-id : ∀ (xs : List X) → xs ↔ xs
↔-id [] = perm-[]
↔-id (x ∷ xs) = perm-cons (justCons (DecSetoid.refl DS) ≋-refl) (↔-id xs)

↔-comm' : ∀ {x xs ys zs} → [ x , zs ]≈ ys → zs ↔ xs → ys ↔ (x ∷ xs)
↔-comm' (justCons x≈y zs≈ys) zs↔xs =
    perm-cons (justCons (DecSetoid.sym DS x≈y) ≋-refl) (↔-subst zs≈ys zs↔xs)
↔-comm' (later z≈y [x,zs]≈ys) (perm-cons [z,as]≈xs zs↔as) =
    perm-cons (later (DecSetoid.refl DS)
                     (insert-subst [z,as]≈xs (DecSetoid.sym DS z≈y)))
              (↔-comm' [x,zs]≈ys zs↔as)

↔-comm : ∀ {xs ys} → xs ↔ ys → ys ↔ xs
↔-comm perm-[] = perm-[]
↔-comm (perm-cons [x,zs]≈ys xs↔zs) = ↔-comm' [x,zs]≈ys (↔-comm xs↔zs)

