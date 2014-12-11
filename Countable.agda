open import Data.Nat
open import Isomorphic

module Countable where

-- A set is countable when it is isomorphic to ℕ
Countable : ∀ {ℓ} → Set ℓ → Set ℓ
Countable A = A ≅ ℕ
