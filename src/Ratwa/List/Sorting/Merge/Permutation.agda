open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Sorting.Merge.Permutation {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt
    renaming (Carrier to X; module Eq to DE)
    using (_≈_; _≟_; _≤_; _≤?_; antisym; total)
open DE using ()
    renaming (setoid to S; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

open import Data.Empty
open import Data.List
    using (List; _∷_; []; splitAt; length; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Pointwise
    using () renaming (_∷_ to _≋-∷_; [] to ≋-[])
open import Data.List.Relation.Equality.Setoid (S)
    using (_≋_; ≋-refl; ≋-sym; ≋-trans)
open import Data.Product using (_,_)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ)
open import Data.Nat using (ℕ; ⌊_/2⌋; suc; zero)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; inspect; [_])
open import Ratwa.List.Compare (dt) using (total-elim)

open import Ratwa.List.Permutation.All (S)
open import Ratwa.List.Sorting.Merge.Sort (dt)

-- when you cannot show ¬ x ≈ y → ¬ y ≈ x ...
merge-commute : ∀ (xs ys : List X) → merge xs ys ≋ merge ys xs
merge-commute [] [] = ≋-refl
merge-commute [] (y ∷ ys) = ≋-refl
merge-commute (x ∷ xs) [] = ≋-refl
merge-commute (x ∷ xs) (y ∷ ys) with x ≟ y | y ≟ x 
... | yes x≈y | no ¬y≈x = ⊥-elim (¬y≈x (≈-sym x≈y))
... | no ¬x≈y | yes y≈x = ⊥-elim (¬x≈y (≈-sym y≈x))
... | yes x≈y | yes y≈x = x≈y ≋-∷ y≈x ≋-∷ (merge-commute xs ys)
... | no ¬x≈y | no ¬y≈x with x ≤? y | y ≤? x
...   | yes x≤y | yes y≤x = ⊥-elim (¬x≈y (antisym x≤y y≤x))
...   | no ¬x≤y | no ¬y≤x = ⊥-elim (¬y≤x (total-elim ¬x≤y))
...   | no ¬x≤y | yes y≤x = ≈-refl ≋-∷ merge-commute (x ∷ xs) ys
...   | yes x≤y | no ¬y≤x = ≈-refl ≋-∷ merge-commute xs (y ∷ ys)

split-++ : ∀ {xs ys zs : List X} {n : ℕ} → (ys , zs) ≡ splitAt n xs → xs ≡ ys ++ zs
split-++ {n = zero} p with ,-injectiveˡ p
... | ys≡[] rewrite ys≡[] | ,-injectiveʳ p = refl
split-++ {[]} {n = suc n} p with ,-injectiveˡ p
... | ys≡[] rewrite ys≡[] | ,-injectiveʳ p = refl
split-++ {x ∷ xs} {n = suc n} p with splitAt n xs | inspect (splitAt n) xs
... | ys' , zs' | [ pp ] with ,-injectiveˡ p
...   | ys≡x∷ys' rewrite ys≡x∷ys' | ,-injectiveʳ p | split-++ {xs} {ys'} {zs'} {n} (sym pp) = refl

split-↔ : ∀ {xs ys zs : List X} {n : ℕ} → (ys , zs) ≡ splitAt n xs → xs ↔ ys ++ zs
split-↔ {xs} {ys} {zs} {n} p rewrite split-++ {xs} {ys} {zs} {n} p = ↔-refl

merge-↔ : ∀ (xs ys : List X) → xs ++ ys ↔ merge xs ys 
merge-↔ [] [] = ↔-refl
merge-↔ [] ys = ↔-refl
merge-↔ xs @ (x ∷ xs') [] rewrite ++-identityʳ xs = ↔-refl
merge-↔ (x ∷ xs) (y ∷ ys) with
    x ≟ y | y ≟ x
... | yes x≈y | no ¬y≈x = ⊥-elim (¬y≈x (≈-sym x≈y))
... | no ¬x≈y | yes y≈x = ⊥-elim (¬x≈y (≈-sym y≈x))
... | yes x≈y | yes y≈x = insHead ≈-refl ≋-refl ∷-↔ ↔-trans
    (↔-sym (insert-↔ {y} {xs} {ys}))
    (insHead ≈-refl ≋-refl ∷-↔ merge-↔ xs ys)
... | no ¬x≈y | no ¬y≈x with x ≤? y | y ≤? x
...   | no ¬x≤y | no ¬y≤x = ⊥-elim (¬y≤x (total-elim ¬x≤y))
...   | yes x≤y | yes y≤x = ⊥-elim (¬x≈y (antisym x≤y y≤x))
...   | yes x≤y | no ¬y≤x = insHead ≈-refl ≋-refl ∷-↔ merge-↔ xs (y ∷ ys)
...   | no ¬x≤y | yes y≤x =
        ↔-trans (↔-sym (insert-↔ {y} {x ∷ xs} {ys}))
                (insHead ≈-refl ≋-refl ∷-↔ merge-↔ (x ∷ xs) ys)

{-# TERMINATING #-}
mergeSortPermuted : ∀ (xs : List X) → xs ↔ mergeSort xs
mergeSortPermuted [] = ↔-[]
mergeSortPermuted xs @ (x ∷ xs₁) with
    halfPartition xs | inspect halfPartition xs
... | left , right | [ eq ] =
    ↔-trans
        (↔-trans
            (split-↔ {xs} {left} {right} {⌊ length xs /2⌋} (sym eq))
            (↔-++ (mergeSortPermuted left) (mergeSortPermuted right)))
        (merge-↔ (mergeSort left) (mergeSort right))
