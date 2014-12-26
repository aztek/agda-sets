open import Level
open import Function
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.EqReasoning as EqR

open import Isomorphic

module Functor (extensionality : ∀ {a b} → Extensionality a b) where

record Functor (F : Set → Set) : Set₁ where
  field
    map : ∀ {A B} → (A → B) → F A → F B
    id-law : ∀ {A} → map {A} id ≗ id
    ∘-law : ∀ {A B C} {f : B → C} {g : A → B} → map f ∘ map g ≗ map (f ∘ g)

open import Data.Maybe as Maybe

MaybeFunctor : Functor Maybe
MaybeFunctor = record
  { map = λ f → maybe (just ∘ f) nothing
  ; id-law = λ { nothing → refl ; (just _) → refl }
  ; ∘-law  = λ { nothing → refl ; (just _) → refl }
  }

≅-lift-functor : ∀ {F} → Functor F →
                 ∀ {A B} → A ≅ B → F A ≅ F B
≅-lift-functor F A≅B = record
  { to = map to
  ; from = map from
  ; inverseˡ = map∘inverseˡ
  ; inverseʳ = map∘inverseʳ
  }
  where
    open Iso A≅B
    open Functor F

    magicˡ = λ x → cong (flip map x) (extensionality inverseˡ)

    map∘inverseˡ = begin
                     map to ∘ map from
                   ≈⟨ ∘-law ⟩
                     map (to ∘ from)
                   ≈⟨ magicˡ ⟩
                     map id
                   ≈⟨ id-law ⟩
                     id
                   ∎ where open EqR (PE._→-setoid_ _ _)

    magicʳ = λ x → cong (flip map x) (extensionality inverseʳ)

    map∘inverseʳ = begin
                     id
                   ≈⟨ sym ∘ id-law ⟩
                     map id
                   ≈⟨ magicʳ ⟩
                     map (from ∘ to)
                   ≈⟨ sym ∘ ∘-law ⟩
                     map from ∘ map to
                   ∎ where open EqR (PE._→-setoid_ _ _)
