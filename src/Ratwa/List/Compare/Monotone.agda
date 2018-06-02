open import Relation.Binary using (DecTotalOrder)

module Ratwa.List.Compare.Monotone {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where
open DecTotalOrder dt renaming (Carrier to X) using ()

open import Level
open import Data.List using (List ; _∷_ ; [] ; _++_)

open import Ratwa.List.Compare (dt)
open import Ratwa.List.Compare.Properties (dt)

infix 3 _↗-∷_

data Monotone : List X → Set (a ⊔ ℓ₂) where
    ↗-[] : Monotone []
    _↗-∷_ : ∀ {x xs} → x ≤* xs → Monotone xs → Monotone (x ∷ xs)

monotone-++ : ∀ {xs ys} → Monotone xs → Monotone ys
              → xs *≤* ys → Monotone (xs ++ ys)
monotone-++ ↗-[] ys xs*≤*ys = ys
monotone-++ (x≤*xs ↗-∷ xs) ys (x≤*ys ∷-*≤* xs*≤*ys) =
    x≤*xs ≤*-++ x≤*ys ↗-∷ monotone-++ xs ys xs*≤*ys
