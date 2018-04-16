open import Relation.Binary using (DecTotalOrder; Setoid)

module Ratwa.List.Compare.Properties {a ℓ₁ ℓ₂} (dt : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder dt renaming (Carrier to X) using
    (_≈_; _≤_; _≤?_; isEquivalence; trans; reflexive)

private
    S : Setoid a ℓ₁
    S = record { Carrier = X; _≈_ = _≈_; isEquivalence = isEquivalence }

open Setoid S renaming (sym to ≈-sym) using ()

open import Level
open import Data.List using (List ; _∷_ ; [] ; _++_; partition)
open import Data.List.Relation.Pointwise using (Pointwise)
open import Data.Product using (_,_; _×_)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; inspect; [_])

open import Ratwa.List.Permutation (S)
open import Ratwa.List.Permutation.Insert (S)
open import Ratwa.List.Compare (dt)

infix 4 _≤≤*_
_≤≤*_ : ∀ {x y zs} → x ≤ y → y ≤* zs → x ≤* zs
x≤y ≤≤* ≤*-[] = ≤*-[]
x≤y ≤≤* (y≤z ≤*-∷ y≤*zs) = trans x≤y y≤z ≤*-∷ (x≤y ≤≤* y≤*zs)

infix 4 _*≤≤*_
_*≤≤*_ : ∀ {xs m ys} → xs *≤ m → m ≤* ys → xs *≤* ys
*≤-[] *≤≤* _ = *≤*-[]
(x≤m ∷-*≤ xs*≤m) *≤≤* m≤*ys = (x≤m ≤≤* m≤*ys) ∷-*≤* (xs*≤m *≤≤* m≤*ys)

≤*-subst : ∀ {xs ys x} → x ≤* xs → Pointwise _≈_ xs ys → x ≤* ys
≤*-subst x≤*xs Pointwise.[] = ≤*-[]
≤*-subst (x≤x' ≤*-∷ x≤*xs) (x'≈y Pointwise.∷ xs≋ys) =
    trans x≤x' (reflexive x'≈y) ≤*-∷ ≤*-subst x≤*xs xs≋ys

≤*-insert : ∀ {x x' xs ys} → x ≤ x' → x ≤* xs → [ x' , xs ]≈ ys → x ≤* ys
≤*-insert x≤x' x≤*xs (insHead x'≈y xs≋ys) =
    (trans x≤x' (reflexive x'≈y)) ≤*-∷ ≤*-subst x≤*xs xs≋ys
≤*-insert x≤x' (x≤x'' ≤*-∷ x≤*xs) (insTail x''≈y [x',xs]≈ys) =
    trans x≤x'' (reflexive x''≈y) ≤*-∷ ≤*-insert x≤x' x≤*xs [x',xs]≈ys

≤*-↔ : ∀ {x xs ys} → x ≤* xs → xs ↔ ys → x ≤* ys
≤*-↔ ≤*-[] perm-[] = ≤*-[]
≤*-↔ (x≤x' ≤*-∷ x≤*xs) (perm-cons [x',zs]≈ys xs↔zs) =
    ≤*-insert x≤x' (≤*-↔ x≤*xs xs↔zs) [x',zs]≈ys

*≤-subst : ∀ {xs ys x} → xs *≤ x → Pointwise _≈_ xs ys → ys *≤ x
*≤-subst xs*≤x Pointwise.[] = *≤-[]
*≤-subst (x'≤x ∷-*≤ xs*≤x) (x'≈y Pointwise.∷ xs≋ys) =
    (trans (reflexive (≈-sym x'≈y)) x'≤x) ∷-*≤ (*≤-subst xs*≤x xs≋ys)

*≤-insert : ∀ {x x' xs ys} → x' ≤ x → xs *≤ x → [ x' , xs ]≈ ys → ys *≤ x
*≤-insert x'≤x xs*≤x (insHead x'≈y xs≋ys) =
    (trans (reflexive (≈-sym x'≈y)) x'≤x) ∷-*≤ (*≤-subst xs*≤x xs≋ys)
*≤-insert x'≤x (x''≤x ∷-*≤ xs*≤x) (insTail x''≈y [x',xs]≈ys) =
    (trans (reflexive (≈-sym x''≈y)) x''≤x)
        ∷-*≤ (*≤-insert x'≤x xs*≤x [x',xs]≈ys)

*≤-↔ : ∀ {x xs ys} → xs *≤ x → xs ↔ ys → ys *≤ x
*≤-↔ xs*≤x perm-[] = *≤-[]
*≤-↔ (x'≤x ∷-*≤ xs*≤x) (perm-cons [x',zs]≈ys xs↔zs) = *≤-insert x'≤x (*≤-↔ xs*≤x xs↔zs) [x',zs]≈ys

infix 4 _≤*-++_
_≤*-++_ : ∀ {x xs ys} → x ≤* xs → x ≤* ys → x ≤* xs ++ ys
_≤*-++_ ≤*-[] x≤*ys = x≤*ys
_≤*-++_ (x≤x' ≤*-∷ x≤*xs) x≤*ys = x≤x' ≤*-∷ x≤*xs ≤*-++ x≤*ys

partition-*≤≤* : ∀ {xs m l r} → (l , r) ≡ partition (λ x → x ≤? m) xs
                                → l *≤ m × m ≤* r
partition-*≤≤* {[]} eq with ,-injectiveˡ eq
... | l≡[] rewrite l≡[] | ,-injectiveʳ eq = *≤-[] , ≤*-[]
partition-*≤≤* {x ∷ xs} {m} eq with
    partition (λ x → x ≤? m) xs | inspect (partition (λ x → x ≤? m)) xs
... | (l' , r') | [ eq' ] with partition-*≤≤* {xs} {m} {l'} {r'} (sym eq')
...   | l'*≤m , m≤*r' with x ≤? m
...     | yes x≤m with ,-injectiveˡ eq
...       | l'≡x∷l rewrite l'≡x∷l | ,-injectiveʳ eq =
                (x≤m ∷-*≤ l'*≤m) , m≤*r'
partition-*≤≤* {x ∷ xs} {m} eq
    | (l' , r') | [ eq' ]
      | l'*≤m , m≤*r'
        | no ¬x≤m with ,-injectiveˡ eq
...       | l'≡l rewrite l'≡l | ,-injectiveʳ eq =
                l'*≤m , ((total-elim ¬x≤m) ≤*-∷ m≤*r')
