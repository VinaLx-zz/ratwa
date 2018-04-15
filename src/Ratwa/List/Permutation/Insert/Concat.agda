open import Relation.Binary using (Setoid)

module Ratwa.List.Permutation.Insert.Concat {a ℓ} (S : Setoid a ℓ) where

open import Ratwa.List.Permutation.Insert (S)

open import Data.List using (List; _∷_; []; _++_)

open import Data.List.Relation.Pointwise using (Pointwise)
open import Data.List.Relation.Equality.Setoid (S)
    using (≋-refl; ≋-sym; ≋-trans)

open Setoid S using (_≈_) renaming
    (Carrier to X; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

private
    ≋-++ : ∀ {xs ys zs zs'} → Pointwise _≈_ xs ys → Pointwise _≈_ zs zs' → Pointwise _≈_ (xs ++ zs) (ys ++ zs')
    ≋-++ Pointwise.[] zs≋zs' = zs≋zs'
    ≋-++ (x≈y Pointwise.∷ xs≋ys) zs≋zs' = x≈y Pointwise.∷ (≋-++ xs≋ys zs≋zs')

insert-++ʳ : ∀ {zs zs' x xs ys} → [ x , xs ]≈ ys → Pointwise _≈_ zs zs' →
             [ x , (xs ++ zs) ]≈ (ys ++ zs')
insert-++ʳ (insHead x≈y xs≈ys) zs≋zs' = insHead x≈y (≋-++ xs≈ys zs≋zs')
insert-++ʳ (insTail x'≈y [x,xs]≈ys ) zs≋zs' =
    insTail x'≈y (insert-++ʳ [x,xs]≈ys zs≋zs')

insert-++ˡ : ∀ {zs zs' x xs ys} → [ x , xs ]≈ ys → Pointwise _≈_ zs zs' →
             [ x , (zs ++ xs) ]≈ (zs' ++ ys)
insert-++ˡ [x,xs]≈ys Pointwise.[] = [x,xs]≈ys
insert-++ˡ [x,xs]≈ys (x≈y Pointwise.∷ zs≋zs') =
    insTail x≈y (insert-++ˡ [x,xs]≈ys zs≋zs')

