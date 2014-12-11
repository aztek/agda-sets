open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as P
import Relation.Binary.EqReasoning as EqR
open import Function
open import Isomorphic

module Isomorphic.Properties where

-- Isomorphism is an equivalence relation
≅-refl : ∀ {ℓ} → Reflexive (_≅_ {ℓ})
≅-refl = record
  { to = id
  ; from = id
  ; inverseˡ = λ _ → refl
  ; inverseʳ = λ _ → refl
  }

≅-sym : ∀ {ℓ₁ ℓ₂} → Sym (_≅_ {ℓ₁}) (_≅_ {ℓ₂})
≅-sym A≅B = record
  { to = from
  ; from = to
  ; inverseˡ = sym ∘ inverseʳ
  ; inverseʳ = sym ∘ inverseˡ
  }
  where open Iso A≅B

≅-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} → Trans (_≅_ {ℓ₁} {ℓ₂}) (_≅_ {ℓ₂} {ℓ₃}) (_≅_ {ℓ₁} {ℓ₃})
≅-trans A≅B B≅C = record
  { to = to₂ ∘ to₁
  ; from = from₁ ∘ from₂
  ; inverseˡ = inverseˡ
  ; inverseʳ = inverseʳ
  }
  where
    open Iso A≅B renaming (to to to₁; from to from₁; inverseˡ to inverseˡ₁; inverseʳ to inverseʳ₁)
    open Iso B≅C renaming (to to to₂; from to from₂; inverseˡ to inverseˡ₂; inverseʳ to inverseʳ₂)

    inverseˡ = begin
                 to₂ ∘ (to₁ ∘ from₁) ∘ from₂
               ≈⟨ cong to₂ ∘ inverseˡ₁ ∘ from₂ ⟩
                 to₂ ∘ from₂
               ≈⟨ inverseˡ₂ ⟩
                 id
               ∎
               where open EqR (P._→-setoid_ _ _)

    inverseʳ = begin
                 id
               ≈⟨ inverseʳ₁ ⟩
                 from₁ ∘ to₁
               ≈⟨ cong from₁ ∘ inverseʳ₂ ∘ to₁ ⟩
                 from₁ ∘ (from₂ ∘ to₂) ∘ to₁
               ∎
               where open EqR (P._→-setoid_ _ _)