open import Relation.Binary using (DecSetoid)

module Ratwa.List.Permutation.Insert.Decidable
    {a ℓ} (DS : DecSetoid a ℓ) where

open import Ratwa.List.Permutation.Insert (DecSetoid.setoid DS)

open import Relation.Nullary using (Dec; yes; no; ¬_)

open DecSetoid DS using (_≈_; _≟_) renaming
    (Carrier to X; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

open import Data.List using (_∷_; []; List)
open import Data.List.Relation.Pointwise using (Pointwise)
open import Data.List.Relation.Equality.DecSetoid (DS)
    using (≋-refl; ≋-sym; ≋-trans; _≋?_)

open import Function using (_$_)

private
    [x,[]]≠[y] : ∀ {x y} → ¬ x ≈ y → ¬ [ x , [] ]≈ (y ∷ [])
    [x,[]]≠[y] ¬x≈y (insHead x≈y _) = ¬x≈y x≈y

    [x,[]]≠y∷ys : ∀ {x y ys} → ¬ Pointwise _≈_ [] ys → ¬ [ x , [] ]≈ (y ∷ ys)
    [x,[]]≠y∷ys ¬[]≋ys (insHead _ []≋ys) = ¬[]≋ys []≋ys

    [x,z∷zs]≠[y∷ys] : ∀ {x z zs y ys} → ¬ Pointwise _≈_ (z ∷ zs) ys → ¬ z ≈ y →
                    ¬ [ x , z ∷ zs ]≈ (y ∷ ys)
    [x,z∷zs]≠[y∷ys] ¬z∷zs≋ys ¬z≈y (insHead _ z∷zs≋ys) = ¬z∷zs≋ys z∷zs≋ys
    [x,z∷zs]≠[y∷ys] ¬z∷zs≋ys ¬z≈y (insTail z≈y _) = ¬z≈y z≈y

    [x,xs]≠y∷xs : ∀ {x y xs ys} → ¬ x ≈ y → Pointwise _≈_ xs ys →
                    ¬ [ x , xs ]≈ (y ∷ ys)
    [x,xs]≠y∷xs ¬x≈y Pointwise.[] = [x,[]]≠[y] ¬x≈y
    [x,xs]≠y∷xs ¬x≈y (x'≈y' Pointwise.∷ xs≋ys) = λ {
        (insHead x≈y _) → ¬x≈y x≈y;
        (insTail x'≈y [x,xs]≈y'∷xs) → [x,xs]≠y∷xs
            (λ x≈y' → ¬x≈y (≈-trans (≈-trans x≈y' $ ≈-sym x'≈y') x'≈y))
            xs≋ys [x,xs]≈y'∷xs}

    insert-weaken : ∀ { x xs ys } → ¬ [ x , xs ]≈ ys →
        ¬ Pointwise _≈_ (x ∷ xs) ys
    insert-weaken ¬[x,xs]≈ys (x≈y Pointwise.∷ x∷xs≋ys) =
        ¬[x,xs]≈ys (insHead x≈y x∷xs≋ys)

    [x,y∷xs]≠y∷ys : ∀ {x y₁ xs y₂ ys} → ¬ [ x , xs ]≈ ys → y₁ ≈ y₂ →
                  ¬ [ x , y₁ ∷ xs ]≈ (y₂ ∷ ys)
    [x,y∷xs]≠y∷ys ¬[x,xs]≠ys _ (insTail _ [x,xs]≈ys) = ¬[x,xs]≠ys [x,xs]≈ys
    [x,y∷xs]≠y∷ys ¬[x,xs]≠ys y₁≈y₂ (insHead x≈y₂ (y₁≈y Pointwise.∷ xs≋ys)) =
        insert-weaken ¬[x,xs]≠ys
            ((≈-trans (≈-trans x≈y₂ $ ≈-sym y₁≈y₂) y₁≈y) Pointwise.∷ xs≋ys)

[_,_]≟_ : ∀ (x : X) → (xs ys : List X) → Dec ([ x , xs ]≈ ys)
[ x , xs ]≟ [] = no $ λ ()
[ x , xs ]≟ (y ∷ ys) with x ≟ y | xs ≋? ys
... | yes x≈y | yes xs≋ys = yes $ insHead x≈y xs≋ys
... | no ¬x≈y | yes xs≋ys = no $ [x,xs]≠y∷xs ¬x≈y xs≋ys
... | _ | no ¬xs≋ys with xs 
...   | [] = no $ [x,[]]≠y∷ys ¬xs≋ys
...   | x₁ ∷ xs₁ with x₁ ≟ y
...     | no ¬x₁≈y = no $ [x,z∷zs]≠[y∷ys] ¬xs≋ys ¬x₁≈y
...     | yes x₁≈y with [ x , xs₁ ]≟ ys
...       | yes [x,xs₁]≈ys = yes $ insTail x₁≈y [x,xs₁]≈ys
...       | no ¬[x,xs₁]≈ys = no $ [x,y∷xs]≠y∷ys ¬[x,xs₁]≈ys x₁≈y

