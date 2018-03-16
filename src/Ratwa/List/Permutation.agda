open import Relation.Binary using (DecSetoid; IsDecEquivalence)

module Ratwa.List.Permutation {a ℓ} (ds : DecSetoid a ℓ) where

open DecSetoid ds renaming (Carrier to X) hiding (_≟_)
open IsDecEquivalence isDecEquivalence

open import Level

open import Data.List using (_∷_; []; List)
open import Data.List.Relation.Pointwise using (Pointwise)

open import Data.List.Relation.Equality.Setoid (DecSetoid.setoid ds)

data [_,_]≈_ : X → List X → List X → Set ℓ where
    justCons : ∀ {x y xs ys} → x ≈ y →
               Pointwise _≈_ xs ys → [ x , xs ]≈ (y ∷ ys)
    later : ∀ {x y z xs xs'} → y ≈ z → 
            [ x , xs ]≈ xs' → [ x , y ∷ xs ]≈ (z ∷ xs')

≈-insert : ∀ {x y xs xs'} → [ x , xs ]≈ xs' → y ≈ x → [ y , xs ]≈ xs'
≈-insert (justCons x≈z xs≈zs) y≈x =
    justCons (DecSetoid.trans ds y≈x x≈z) xs≈zs
≈-insert (later z≈z' ins) y≈x = later z≈z' (≈-insert ins y≈x)

-- Permutation

data _↔_ : List X → List X → Set (a ⊔ ℓ) where
    perm-[] : [] ↔ []
    perm-cons : ∀ {x xs ys xs'} →
                [ x , ys ]≈ xs' → xs ↔ ys → (x ∷ xs) ↔ xs'

≈-perm : ∀ {xs ys zs} → Pointwise _≈_ xs ys → xs ↔ zs → ys ↔ zs
≈-perm Pointwise.[] perm-[] = perm-[]
≈-perm (x~y Pointwise.∷ xs~ys) (perm-cons p perm) =
    perm-cons (≈-insert p (DecSetoid.sym ds x~y)) (≈-perm xs~ys perm)

↔-id : ∀ (xs : List X) → xs ↔ xs
↔-id [] = perm-[]
↔-id (x ∷ xs) = perm-cons (justCons (DecSetoid.refl ds) ≋-refl) (↔-id xs)

↔-comm' : ∀ {x xs ys zs} → [ x , zs ]≈ ys → zs ↔ xs → ys ↔ (x ∷ xs)
↔-comm' {ys = (y ∷ ys')} (justCons eq eqs) zsxs =
    perm-cons (justCons (DecSetoid.sym ds eq) ≋-refl) (≈-perm eqs zsxs)
↔-comm' (later p xzs) (perm-cons p' zsxs) =
    perm-cons (later (DecSetoid.refl ds) (≈-insert p' (DecSetoid.sym ds p)))
              (↔-comm' xzs zsxs)

↔-comm : ∀ {xs ys} → xs ↔ ys → ys ↔ xs
↔-comm perm-[] = perm-[]
↔-comm (perm-cons xzs p) = ↔-comm' xzs (↔-comm p)

