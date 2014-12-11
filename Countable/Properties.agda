open import Data.Nat
open import Function

open import Isomorphic
open import Finite
open import Finite.Properties
open import Countable
open import Relation.Binary.Core

module Countable.Properties where

-- A countable set is infinite
countable-infinite : ∀ {ℓ} {A : Set ℓ} → Countable A → Infinite A
countable-infinite countable = ℕ-infinite ∘ finite-iso countable
