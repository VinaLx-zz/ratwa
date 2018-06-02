open import Relation.Binary using (Setoid)

module Ratwa.List.Permutation.All {a ℓ} (S : Setoid a ℓ) where

open import Ratwa.List.Permutation (S) public
open import Ratwa.List.Permutation.Concat (S) public
open import Ratwa.List.Permutation.Insert (S) public
open import Ratwa.List.Permutation.Setoid (S) public

