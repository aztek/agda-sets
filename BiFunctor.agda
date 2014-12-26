open import Level
open import Function
open import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.EqReasoning as EqR

open import Isomorphic

module BiFunctor (extensionality : ∀ {a b} → Extensionality a b) where

record BiFunctor (F : Set → Set → Set) : Set₁ where
  field
    map : ∀ {A B C D} → (A → B) → (C → D) → F A C → F B D
    id-law : ∀ {A C} → map {A = A} {C = C} id id ≗ id
    ∘-law : ∀ {A B C D E G} {f₁ : B → E} {f₂ : D → G} {g₁ : A → B} {g₂ : C → D} →
            map f₁ f₂ ∘ map g₁ g₂ ≗ map (f₁ ∘ g₁) (f₂ ∘ g₂)

open import Data.Sum as S using (_⊎_; [_,_])

⊎-bifunctor : BiFunctor _⊎_
⊎-bifunctor = record
  { map    = S.map
  ; id-law = [ (λ _ → refl) , (λ _ → refl) ]
  ; ∘-law  = [ (λ _ → refl) , (λ _ → refl) ]
  }

open import Data.Product as P using (_×_; _,_)

×-bifunctor : BiFunctor _×_
×-bifunctor = record
  { map    = λ f g → P.map f g
  ; id-law = λ { (_ , _) → refl }
  ; ∘-law  = λ { (_ , _) → refl }
  }

≅-lift-bifunctor : ∀ {F} → BiFunctor F → ∀ {A B C D} → A ≅ B → C ≅ D → F A C ≅ F B D
≅-lift-bifunctor bf A≅B C≅D = record
  { to = map I₁.to I₂.to
  ; from = map I₁.from I₂.from
  ; inverseˡ = inverseˡ
  ; inverseʳ = inverseʳ
  }
  where
    module I₁ = Iso A≅B
    module I₂ = Iso C≅D
    open BiFunctor bf

    magicˡ = λ x → cong₂ (λ f g → map f g x) (extensionality I₁.inverseˡ) (extensionality I₂.inverseˡ)

    inverseˡ = begin
                  map I₁.to I₂.to ∘ map I₁.from I₂.from
               ≈⟨ ∘-law ⟩
                 map (I₁.to ∘ I₁.from) (I₂.to ∘ I₂.from)
               ≈⟨ magicˡ ⟩
                 map id id
               ≈⟨ id-law ⟩
                 id
               ∎ where open EqR (PE._→-setoid_ _ _)

    magicʳ = λ x → cong₂ (λ f g → map f g x) (extensionality I₁.inverseʳ) (extensionality I₂.inverseʳ)

    inverseʳ = begin
                 id
               ≈⟨ sym ∘ id-law ⟩
                 map id id
               ≈⟨ magicʳ ⟩
                 map (I₁.from ∘ I₁.to) (I₂.from ∘ I₂.to)
               ≈⟨ sym ∘ ∘-law ⟩
                 map I₁.from I₂.from ∘ map I₁.to I₂.to
               ∎ where open EqR (PE._→-setoid_ _ _)
