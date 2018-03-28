open import Relation.Binary using (Setoid)

module Ratwa.List.Permutation.Insert.Membership
    {a ℓ} (S : Setoid a ℓ) where

open Setoid S using (_≈_) renaming
    (Carrier to X; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

open import Ratwa.List.Permutation.Insert (S)

open import Data.List using (_∷_; []; List)
open import Data.List.Relation.Equality.Setoid (S) using (≋-refl)
open import Data.List.Any using (here; there)
open import Data.List.Any.Membership (S) using (_∈_)

open import Data.Product using (∃; _,_)

insert→any : ∀ {x xs ys} → [ x , xs ]≈ ys → x ∈ ys
insert→any (insHead x≈y xs≈ys) = here x≈y
insert→any (insTail x'≈y' [x,xs]≈ys) = there (insert→any [x,xs]≈ys)

any→insert : ∀ {x ys} → x ∈ ys → ∃ λ xs → [ x , xs ]≈ ys
any→insert (here {xs = xs} x≈y) = xs , insHead x≈y ≋-refl
any→insert (there {x = x} x∈ys) with any→insert x∈ys
... | xs , [x,xs]≈ys = (x ∷ xs) , (insTail ≈-refl [x,xs]≈ys)

