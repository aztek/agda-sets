open import Data.Fin using (Fin; zero; suc)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Vec
open import Data.Product
open import Relation.Nullary.Core
open import Isomorphic

module Finity where

-- A set is finite when it's isomorphic to Fin ℵ
record Finite {ℓ} (A : Set ℓ) : Set ℓ where
  field
    ℵ : ℕ
    iso : A ≅ Fin ℵ

-- Conversely, a set is infinite when it's not finite
Infinite : ∀ {ℓ} → Set ℓ → Set ℓ
Infinite A = ¬ Finite A

-- If a set is finite, we can put all its elements in a vector,
-- that we call a table
table : ∀ {ℓ} {A : Set ℓ} (finite : Finite A) → Vec A (Finite.ℵ finite)
table finite = tabulate from where open Finite finite; open Iso iso

-- All elements of a finite set are in its table
finite-table : ∀ {ℓ} {A : Set ℓ} (finite : Finite A) → ∀ a → a ∈ table finite
finite-table finite a
  with to a | inverseʳ a where open Finite finite; open Iso iso
...  | i    | a=from[i] rewrite a=from[i] = ∈-tabulate i
  where
    ∈-tabulate : ∀ {ℓ} {A : Set ℓ} {ℵ} {f : Fin ℵ → A} i → f i ∈ tabulate f
    ∈-tabulate zero = here
    ∈-tabulate (suc i) = there (∈-tabulate i)
