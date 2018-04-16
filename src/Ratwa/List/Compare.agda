open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Compare {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using (_≤_; total)

open import Level
open import Data.List using (List ; _∷_ ; [])

open import Relation.Nullary using (¬_)
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)

total-elim : ∀ {x y} → ¬ x ≤ y → y ≤ x
total-elim {x} {y} ¬x≤y with total x y
... | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
... | inj₂ y≤x = y≤x

infix 4 _≤*_ _*≤*_ _*≤_
infix 3 _≤*-∷_ _∷-*≤*_ _∷-*≤_

data _≤*_ (x : X) : List X → Set (a ⊔ ℓ₂) where
    ≤*-[] : x ≤* []
    _≤*-∷_ : ∀ {x' xs} → x ≤ x' → x ≤* xs → x ≤* x' ∷ xs

data _*≤_ : List X → X → Set (a ⊔ ℓ₂) where
    *≤-[] : ∀ {x} → [] *≤ x
    _∷-*≤_ : ∀ {x xs x'} → x ≤ x' → xs *≤ x' → x ∷ xs *≤ x'

data _*≤*_ : List X → List X → Set (a ⊔ ℓ₂) where
    *≤*-[] : ∀ {xs} → [] *≤* xs
    _∷-*≤*_ : ∀ {x xs ys} → x ≤* ys → xs *≤* ys → x ∷ xs *≤* ys

_*≤*-∷_ : ∀ {xs y ys} → xs *≤ y → xs *≤* ys → xs *≤* y ∷ ys
_*≤*-∷_ {[]} _ _ = *≤*-[]
_*≤*-∷_ {x ∷ xs} (x≤y ∷-*≤ xs*≤y) (x≤*ys ∷-*≤* xs*≤*ys) =
    (x≤y ≤*-∷ x≤*ys) ∷-*≤* (xs*≤y *≤*-∷ xs*≤*ys)

