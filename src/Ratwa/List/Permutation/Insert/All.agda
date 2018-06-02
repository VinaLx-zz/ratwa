open import Relation.Binary using (Setoid)

module Ratwa.List.Permutation.Insert.All {a ℓ} (S : Setoid a ℓ) where

open import Ratwa.List.Permutation.Insert (S) public
open import Ratwa.List.Permutation.Insert.Concat (S) public
open import Ratwa.List.Permutation.Insert.Membership (S) public

