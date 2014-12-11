open import Function
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec
open import Data.Product
open import Relation.Nullary.Core
open import Data.Empty

open import Isomorphic.Properties
open import Finite

module Finite.Properties where

open import Data.Nat
open import Data.Nat.Properties

open import Isomorphic
open import Relation.Binary.Core

-- Any set, isomorphic to a finite one is finite
finite-iso : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A ≅ B → Finite A → Finite B
finite-iso A≅B f = record
  { ℵ = Finite.ℵ f
  ; iso = ≅-trans (≅-sym A≅B) (Finite.iso f)
  }

-- The set of naturals is infinite
ℕ-infinite : Infinite ℕ
ℕ-infinite finite = contradiction
  where
    -- Lemma: for an arbitrary vector of naturals we can find
    -- a natural that is not in it
    ∃x∉xs : ∀ {n} (xs : Vec ℕ n) → ∃ λ x → ¬ x ∈ xs
    ∃x∉xs xs = suc (sum xs) , n≮n ∘ ≤-sum xs
      where
        n≮n : ∀ {n} → ¬ n < n
        n≮n (s≤s n<n) = n≮n n<n

        ≤-sum : ∀ {n} (xs : Vec ℕ n) → ∀ {x} → x ∈ xs → x ≤ sum xs
        ≤-sum (x ∷ xs) here = m≤m+n x (sum xs)
        ≤-sum (x ∷ xs) (there x∈xs) = ≤-steps x (≤-sum xs x∈xs)

    ∀n∈table = finite-table finite _
    ∃n∉table = ∃x∉xs _
    contradiction = proj₂ ∃n∉table ∀n∈table


-- ⊥ is finite (duh)
⊥-finite : Finite ⊥
⊥-finite = record
  { ℵ = zero
  ; iso = record
    { to = λ ()
    ; from = λ ()
    ; inverseˡ = λ ()
    ; inverseʳ = λ ()
    }
  }
{-
-- Product of finite set is finite
×-finite : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) → Finite A → Finite B → Finite (A × B)
×-finite A₁ A₂ f₁ f₂ = record
  { ℵ = ℵ
  ; iso = record
    { to = to
    ; from = from
    ; inverseˡ = {!!}
    ; inverseʳ = {!!}
    }
  }
  where
    ℵ₁ = Finite.ℵ f₁
    ℵ₂ = Finite.ℵ f₂

    ℵ = ℵ₁ * ℵ₂

    to : A₁ × A₂ → Fin ℵ
    to (a₁ , a₂) = {!!}
      where n₁ = Iso.to (Finite.iso f₁) a₁
            n₂ = Iso.to (Finite.iso f₂) a₂
    
    from : Fin ℵ → A₁ × A₂
    from n = {!!} , {!!}
--      where a₁ = Iso.from (Finite.iso f₁) n
--            a₂ = Iso.from (Finite.iso f₂) n
-}
