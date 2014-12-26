open import Data.Nat
open import Function
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

open import Isomorphic
open import Finity
open import Countable

module Countable.Properties (extensionality : ∀ {a b} → Extensionality a b) where

open import Isomorphic.Properties (extensionality)
open import Finity.Properties (extensionality)

-- A countable set is infinite
countable-infinite : ∀ {ℓ} {A : Set ℓ} → Countable A → Infinite A
countable-infinite countable = ℕ-infinite ∘ finite-iso countable

-- If a countable set is isomorphic to another one, it is also countable
countable-iso : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A ≅ B → Countable A → Countable B
countable-iso A≅B = ≅-trans (≅-sym A≅B)
