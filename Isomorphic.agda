open import Level using (_⊔_)
open import Function
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

module Isomorphic where

-- Two sets are isomorphic when there is a bijection between them
record Iso {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to   : A → B
    from : B → A
    
    inverseˡ : to ∘ from ≗ id
    inverseʳ : id ≗ from ∘ to

infix 0 _≅_
_≅_ : ∀ {ℓ₁ ℓ₂} → REL (Set ℓ₁) (Set ℓ₂) (ℓ₁ ⊔ ℓ₂)
A ≅ B = Iso A B
