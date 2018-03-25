open import Relation.Binary using (Setoid)

module Ratwa.List.Permutation.Insert {a ℓ} (S : Setoid a ℓ) where

open import Data.List using (List; _∷_)
open import Data.List.Relation.Pointwise using (Pointwise)
open import Data.List.Relation.Equality.Setoid (S)
    using (≋-refl; ≋-sym; ≋-trans)

open Setoid S using (_≈_) renaming
    (Carrier to X; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

open import Function using (_$_)
open import Data.Product using (∃; _,_; _×_)

data [_,_]≈_ : X → List X → List X → Set ℓ where
    insHead : ∀ {x y xs ys} → x ≈ y →
               Pointwise _≈_ xs ys → [ x , xs ]≈ (y ∷ ys)
    insTail : ∀ {x y z xs xs'} → y ≈ z → 
            [ x , xs ]≈ xs' → [ x , y ∷ xs ]≈ (z ∷ xs')

insert-subst₁ : ∀ {x y xs xs'} → x ≈ y → [ x , xs ]≈ xs' → [ y , xs ]≈ xs'
insert-subst₁ x≈y (insHead x≈z xs≈zs) =
    insHead (≈-trans (≈-sym x≈y) x≈z) xs≈zs
insert-subst₁ x≈y (insTail z≈z' [x,xs]≈xs') =
    insTail z≈z' $ insert-subst₁ x≈y [x,xs]≈xs'

insert-subst₂ : ∀ {x xs₁ xs₂ xs} → Pointwise _≈_ xs₁ xs₂ →
                [ x , xs₁ ]≈ xs → [ x , xs₂ ]≈ xs
insert-subst₂ xs₁≈xs₂ (insHead x≈x' xs₁≈xs) =
    insHead x≈x' (≋-trans (≋-sym xs₁≈xs₂) xs₁≈xs)
insert-subst₂ (x₁≈x₂ Pointwise.∷ xs₁≈xs₂) (insTail x₁≈x' [x,xs₁]≈xs) = 
    insTail (≈-trans (≈-sym x₁≈x₂) x₁≈x') (insert-subst₂ xs₁≈xs₂ [x,xs₁]≈xs)

insert-subst₃ : ∀ {x xs xs₁ xs₂} → Pointwise _≈_ xs₁ xs₂ →
                [ x , xs ]≈ xs₁ → [ x , xs ]≈ xs₂
insert-subst₃ (x₁≈x₂ Pointwise.∷ xs₁≈xs₂) (insHead x≈x₁ xs≈xs₁) =
    insHead (≈-trans x≈x₁ x₁≈x₂) (≋-trans xs≈xs₁ xs₁≈xs₂)
insert-subst₃ (x₁≈x₂ Pointwise.∷ xs₁≈xs₂) (insTail x'≈x₁ [x,xs]≈xs₁) =
    insTail (≈-trans x'≈x₁ x₁≈x₂) (insert-subst₃ xs₁≈xs₂ [x,xs]≈xs₁)

-- commutativity of insert

insert-comm : ∀ {x y s xs xys} → [ x , s ]≈ xs → [ y , xs ]≈ xys →
               ∃ \ys → ([ y , s ]≈ ys) × ([ x , ys ]≈ xys)
insert-comm p (insHead y≈y₁ xs≈xs₁) = _ ,  -- y ∷ s
    (insHead ≈-refl ≋-refl , insTail y≈y₁ (insert-subst₃ xs≈xs₁ p))
insert-comm (insHead x≈x' s≈xs) (insTail x'≈xy' [y,xs]≈xys) = _ , -- xys
    insert-subst₂ (≋-sym s≈xs) [y,xs]≈xys ,
    insHead (≈-trans x≈x' x'≈xy') ≋-refl
insert-comm (insTail sx≈x' [x,s]≈xs) (insTail x'≈xy' [y,xs]≈xys)
    with insert-comm [x,s]≈xs [y,xs]≈xys
... | ys , [y,s]≈ys , [x,ys]≈xys = _ ,   -- sx ∷ ys
      insTail ≈-refl [y,s]≈ys , insTail (≈-trans sx≈x' x'≈xy') [x,ys]≈xys

