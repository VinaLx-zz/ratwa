open import Relation.Binary using (Setoid)

module Ratwa.List.Permutation.Concat {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to X; refl to ≈-refl) hiding (sym)

open import Ratwa.List.Permutation (S) using (perm-[]; perm-cons; _↔_)
open import Ratwa.List.Permutation.Insert (S)
open import Ratwa.List.Permutation.Insert.Concat (S) using (insert-++ʳ)
open import Ratwa.List.Permutation.Setoid (S) using (↔-sym)

open import Data.List using (_∷_; []; List; partition; _++_)
open import Data.List.Relation.Equality.Setoid (S)
open import Data.List.Properties using (++-identityʳ)

open import Relation.Binary.PropositionalEquality using
    (_≡_; refl; sym; inspect; [_])
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable)

open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ)

partition-↔-++ : ∀ {xs l r} {p} {P : X → Set p} {p? : Decidable P} →
                 (l , r) ≡ partition p? xs → xs ↔ (l ++ r)

partition-↔-++ {[]} eq with ,-injectiveˡ eq
... | l≡[] rewrite l≡[] | ,-injectiveʳ eq = perm-[]

partition-↔-++ {x ∷ xs} {p? = p} eq with p x | partition p xs
                                       | inspect (partition p) xs
partition-↔-++ {x ∷ xs} {p? = p} eq | yes px | ys , zs | [ pp ]
    with ,-injectiveˡ eq 
... | l≡x∷ys rewrite l≡x∷ys | ,-injectiveʳ eq =
    perm-cons (insHead ≈-refl ≋-refl) (partition-↔-++ (sym pp))
partition-↔-++ {x ∷ xs} {p? = p} eq | no ¬px | ys , zs | [ pp ]
    with ,-injectiveˡ eq
... | l≡ys rewrite l≡ys | ,-injectiveʳ eq =
    perm-cons (insert x ys zs) (partition-↔-++ (sym pp))

↔-++ : ∀ {xs₁ xs₂ ys₁ ys₂} → xs₁ ↔ ys₁ → xs₂ ↔ ys₂ → (xs₁ ++ xs₂) ↔ (ys₁ ++ ys₂)
↔-++ perm-[] xs₂↔ys₂ = xs₂↔ys₂
-- ↔-++ {xs₁ = xs₁} {ys₁ = ys₁} xs₁↔ys₁ perm-[]
    -- rewrite ++-identityʳ xs₁ | ++-identityʳ ys₁ = xs₁↔ys₁
↔-++ {x₁ ∷ xs₁} {xs₂} {ys₁} {ys₂}
    (perm-cons {ys = zs₁} [x₁,zs₁]≈ys₁ xs₁↔zs₁) xs₂↔ys₂ =
    perm-cons (insert-++ʳ {ys₂} [x₁,zs₁]≈ys₁ ≋-refl) (↔-++ xs₁↔zs₁ xs₂↔ys₂)

