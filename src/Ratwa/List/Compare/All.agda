open import Relation.Binary using (DecTotalOrder)

module Ratwa.List.Compare.All {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open import Ratwa.List.Compare (dt) public
open import Ratwa.List.Compare.Monotone (dt) public
open import Ratwa.List.Compare.Properties (dt) public

