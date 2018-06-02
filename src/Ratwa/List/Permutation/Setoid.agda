open import Relation.Binary using (Setoid; IsEquivalence)

module Ratwa.List.Permutation.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S using (_≈_) renaming
    (Carrier to X; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

open import Data.List using (_∷_; []; List)
open import Data.List.Relation.Equality.Setoid (S)
    using (≋-refl; ≋-sym; ≋-trans)

open import Ratwa.List.Permutation.Insert (S)
open import Ratwa.List.Permutation (S)

open import Function using (_$_)
open import Data.Product using (∃; _,_; _×_)

↔-refl : ∀ {xs : List X} → xs ↔ xs
↔-refl {[]} = ↔-[]
↔-refl {x ∷ xs} = insHead ≈-refl ≋-refl ∷-↔ ↔-refl

private
    ↔-sym' : ∀ {x xs ys zs} → [ x , zs ]≈ ys → zs ↔ xs → ys ↔ (x ∷ xs)
    ↔-sym' (insHead x≈y zs≈ys) zs↔xs =
        insHead (≈-sym x≈y) ≋-refl ∷-↔ ↔-subst₁ zs≈ys zs↔xs
    ↔-sym' (insTail z≈y [x,zs]≈ys) ([z,as]≈xs ∷-↔ zs↔as) =
        insTail ≈-refl (insert-subst₁ z≈y [z,as]≈xs)
            ∷-↔ (↔-sym' [x,zs]≈ys zs↔as)

↔-sym : ∀ {xs ys} → xs ↔ ys → ys ↔ xs
↔-sym ↔-[] = ↔-[]
↔-sym ([x,zs]≈ys ∷-↔ xs↔zs) = ↔-sym' [x,zs]≈ys (↔-sym xs↔zs)

private
    ↔-trans' : ∀ {x bs ys zs} → [ x , bs ]≈ ys → ys ↔ zs →
               ∃ \cs → ([ x , cs ]≈ zs) × (bs ↔ cs)
    ↔-trans' (insHead x≈y bs≈ys) ([y,cs]≈zs ∷-↔ ys↔cs) =
        _ , insert-subst₁ (≈-sym x≈y) [y,cs]≈zs , ↔-subst₁ (≋-sym bs≈ys) ys↔cs
    ↔-trans' (insTail b≈y [x,bs]≈ys) ([y,ds]≈zs ∷-↔ ys↔ds)
        with ↔-trans' [x,bs]≈ys ys↔ds
        -- b≈y [y,ds]≈zs  ==> cs , [x,cs]≈zs , b∷bs↔cs (i.e. [b,es]≈cs bs↔es)
    ... | es , [x,es]≈ds , bs↔es with insert-comm [x,es]≈ds [y,ds]≈zs
    ...     | cs , [y,es]≈cs , [x,cs]≈zs = cs , [x,cs]≈zs ,
                insert-subst₁ (≈-sym b≈y) [y,es]≈cs ∷-↔ bs↔es

↔-trans : ∀ {xs ys zs} → xs ↔ ys → ys ↔ zs → xs ↔ zs
↔-trans ↔-[] ↔-[] = ↔-[]
↔-trans ([x,bs]≈ys ∷-↔ xs↔bs) ys↔zs with ↔-trans' [x,bs]≈ys ys↔zs
... | cs , [x,cs]≈zs , bs↔cs = [x,cs]≈zs ∷-↔ (↔-trans xs↔bs bs↔cs)

isEquivalence : IsEquivalence _↔_
isEquivalence = record { refl = ↔-refl; sym = ↔-sym; trans = ↔-trans }

setoid : Setoid _ _
setoid = record { Carrier = List X; _≈_ = _↔_; isEquivalence = isEquivalence }

