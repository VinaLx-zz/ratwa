open import Relation.Binary using (DecSetoid; IsDecEquivalence)

module Ratwa.List.Permutation {a ℓ} (DS : DecSetoid a ℓ) where

open DecSetoid DS renaming
    (Carrier to X; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans) hiding (_≟_)
open IsDecEquivalence isDecEquivalence

open import Level

open import Data.List using (_∷_; []; List)
open import Data.List.Relation.Pointwise using (Pointwise)
open import Function using (_$_)

open import Data.List.Relation.Equality.Setoid (DecSetoid.setoid DS)

data [_,_]≈_ : X → List X → List X → Set ℓ where
    justCons : ∀ {x y xs ys} → x ≈ y →
               Pointwise _≈_ xs ys → [ x , xs ]≈ (y ∷ ys)
    later : ∀ {x y z xs xs'} → y ≈ z → 
            [ x , xs ]≈ xs' → [ x , y ∷ xs ]≈ (z ∷ xs')

insert-subst : ∀ {x y xs xs'} → x ≈ y → [ x , xs ]≈ xs' → [ y , xs ]≈ xs'
insert-subst x≈y (justCons x≈z xs≈zs) =
    justCons (≈-trans (≈-sym x≈y) x≈z) xs≈zs
insert-subst x≈y (later z≈z' [x,xs]≈xs') =
    later z≈z' $ insert-subst x≈y [x,xs]≈xs'

-- Permutation

data _↔_ : List X → List X → Set (a ⊔ ℓ) where
    perm-[] : [] ↔ []
    perm-cons : ∀ {x xs ys xs'} →
                [ x , ys ]≈ xs' → xs ↔ ys → (x ∷ xs) ↔ xs'

↔-subst₁ : ∀ {xs ys zs} → Pointwise _≈_ xs ys → xs ↔ zs → ys ↔ zs
↔-subst₁ Pointwise.[] perm-[] = perm-[]
↔-subst₁ (x≈y Pointwise.∷ xs≈ys) (perm-cons [x,as]≈zs xs↔as) =
    perm-cons (insert-subst x≈y [x,as]≈zs) (↔-subst₁ xs≈ys xs↔as)

↔-refl : ∀ (xs : List X) → xs ↔ xs
↔-refl [] = perm-[]
↔-refl (x ∷ xs) = perm-cons (justCons ≈-refl ≋-refl) (↔-refl xs)

private
    ↔-sym' : ∀ {x xs ys zs} → [ x , zs ]≈ ys → zs ↔ xs → ys ↔ (x ∷ xs)
    ↔-sym' (justCons x≈y zs≈ys) zs↔xs =
        perm-cons (justCons (≈-sym x≈y) ≋-refl) (↔-subst₁ zs≈ys zs↔xs)
    ↔-sym' (later z≈y [x,zs]≈ys) (perm-cons [z,as]≈xs zs↔as) =
        perm-cons (later ≈-refl $ insert-subst z≈y [z,as]≈xs)
                (↔-sym' [x,zs]≈ys zs↔as)

↔-sym : ∀ {xs ys} → xs ↔ ys → ys ↔ xs
↔-sym perm-[] = perm-[]
↔-sym (perm-cons [x,zs]≈ys xs↔zs) = ↔-sym' [x,zs]≈ys (↔-sym xs↔zs)

↔-subst₂ : ∀ {xs ys zs} → Pointwise _≈_ ys zs → xs ↔ ys → xs ↔ zs
↔-subst₂ ys≈zs xs↔ys = ↔-sym $ ↔-subst₁ ys≈zs $ ↔-sym xs↔ys

↔-trans : ∀ {xs ys zs} → xs ↔ ys → ys ↔ zs → xs ↔ zs
↔-trans perm-[] perm-[] = perm-[]
↔-trans (perm-cons [x,bs]≈ys xs↔bs) ys↔zs = ?
