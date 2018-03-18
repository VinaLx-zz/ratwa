open import Relation.Binary using (IsEquivalence; Setoid; DecSetoid; IsDecEquivalence)

module Ratwa.List.Permutation {a ℓ} (DS : DecSetoid a ℓ) where

open DecSetoid DS using (_≈_; _≟_) renaming
    (Carrier to X; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

open import Data.List using (_∷_; []; List)
open import Data.List.Relation.Pointwise using (Pointwise)
open import Data.List.Relation.Equality.DecSetoid (DS)
    using (≋-refl; ≋-sym; ≋-trans; _≋?_)

open import Level using (_⊔_)
open import Data.Product using (∃; _,_; _×_)
open import Function using (_$_)

open import Relation.Nullary using (Dec; yes; no; ¬_)

-- [ x , xs ]≈ ys
-- insert `x` into `xs` somewhere would be equal (in terms of _≈_) to `ys`
data [_,_]≈_ : X → List X → List X → Set ℓ where
    insHead : ∀ {x y xs ys} → x ≈ y →
               Pointwise _≈_ xs ys → [ x , xs ]≈ (y ∷ ys)
    insTail : ∀ {x y z xs xs'} → y ≈ z → 
            [ x , xs ]≈ xs' → [ x , y ∷ xs ]≈ (z ∷ xs')

-- substitution (rewriting) in terms of _≈_ and Pointwise _≈_

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

-- decide

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

-- permutation

data _↔_ : List X → List X → Set (a ⊔ ℓ) where
    perm-[] : [] ↔ []
    perm-cons : ∀ {x xs ys xs'} →
                [ x , ys ]≈ xs' → xs ↔ ys → (x ∷ xs) ↔ xs'

-- substitution (rewriting) in terms of Pointwise _≈_

↔-subst₁ : ∀ {xs ys zs} → Pointwise _≈_ xs ys → xs ↔ zs → ys ↔ zs
↔-subst₁ Pointwise.[] perm-[] = perm-[]
↔-subst₁ (x≈y Pointwise.∷ xs≈ys) (perm-cons [x,as]≈zs xs↔as) =
    perm-cons (insert-subst₁ x≈y [x,as]≈zs) (↔-subst₁ xs≈ys xs↔as)

↔-refl : ∀ {xs : List X} → xs ↔ xs
↔-refl {[]} = perm-[]
↔-refl {x ∷ xs} = perm-cons (insHead ≈-refl ≋-refl) ↔-refl

private
    ↔-sym' : ∀ {x xs ys zs} → [ x , zs ]≈ ys → zs ↔ xs → ys ↔ (x ∷ xs)
    ↔-sym' (insHead x≈y zs≈ys) zs↔xs =
        perm-cons (insHead (≈-sym x≈y) ≋-refl) (↔-subst₁ zs≈ys zs↔xs)
    ↔-sym' (insTail z≈y [x,zs]≈ys) (perm-cons [z,as]≈xs zs↔as) =
        perm-cons (insTail ≈-refl $ insert-subst₁ z≈y [z,as]≈xs)
                  (↔-sym' [x,zs]≈ys zs↔as)

↔-sym : ∀ {xs ys} → xs ↔ ys → ys ↔ xs
↔-sym perm-[] = perm-[]
↔-sym (perm-cons [x,zs]≈ys xs↔zs) = ↔-sym' [x,zs]≈ys (↔-sym xs↔zs)

↔-subst₂ : ∀ {xs ys zs} → Pointwise _≈_ ys zs → xs ↔ ys → xs ↔ zs
↔-subst₂ ys≈zs xs↔ys = ↔-sym $ ↔-subst₁ ys≈zs $ ↔-sym xs↔ys

private
    ↔-trans' : ∀ {x bs ys zs} → [ x , bs ]≈ ys → ys ↔ zs →
               ∃ \cs → ([ x , cs ]≈ zs) × (bs ↔ cs)
    ↔-trans' (insHead x≈y bs≈ys) (perm-cons [y,cs]≈zs ys↔cs) =
        _ , insert-subst₁ (≈-sym x≈y) [y,cs]≈zs , ↔-subst₁ (≋-sym bs≈ys) ys↔cs
    ↔-trans' (insTail b≈y [x,bs]≈ys) (perm-cons [y,ds]≈zs ys↔ds)
        with ↔-trans' [x,bs]≈ys ys↔ds
        -- b≈y [y,ds]≈zs  ==> cs , [x,cs]≈zs , b∷bs↔cs (i.e. [b,es]≈cs bs↔es)
    ... | es , [x,es]≈ds , bs↔es with insert-comm [x,es]≈ds [y,ds]≈zs
    ...     | cs , [y,es]≈cs , [x,cs]≈zs = cs , [x,cs]≈zs ,
                perm-cons (insert-subst₁ (≈-sym b≈y) [y,es]≈cs) bs↔es

↔-trans : ∀ {xs ys zs} → xs ↔ ys → ys ↔ zs → xs ↔ zs
↔-trans perm-[] perm-[] = perm-[]
↔-trans (perm-cons [x,bs]≈ys xs↔bs) ys↔zs with ↔-trans' [x,bs]≈ys ys↔zs
... | cs , [x,cs]≈zs , bs↔cs = perm-cons [x,cs]≈zs (↔-trans xs↔bs bs↔cs)

isEquivalence : IsEquivalence _↔_
isEquivalence = record { refl = ↔-refl; sym = ↔-sym; trans = ↔-trans }

setoid : Setoid _ _
setoid = record { Carrier = List X; _≈_ = _↔_; isEquivalence = isEquivalence }

