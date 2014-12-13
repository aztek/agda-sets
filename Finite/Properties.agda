open import Function
open import Data.Fin using (Fin; zero; suc)
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

open import Isomorphic
open import Isomorphic.Properties
open import Finite

module Finite.Properties where

-- Bool is finite
open import Data.Bool

Bool-finite : Finite Bool
Bool-finite = record
  { ℵ = 2
  ; iso = record
    { to = to
    ; from = from
    ; inverseˡ = inverseˡ
    ; inverseʳ = inverseʳ
    }
  }
  where
    to : Bool → Fin 2
    to true = zero
    to false = suc zero

    from : Fin 2 → Bool
    from zero = true
    from (suc zero) = false
    from (suc (suc ()))

    inverseˡ : to ∘ from ≗ id
    inverseˡ zero = refl
    inverseˡ (suc zero) = refl
    inverseˡ (suc (suc ()))

    inverseʳ : id ≗ from ∘ to
    inverseʳ true = refl
    inverseʳ false = refl

-- ⊥ is finite (duh)
open import Data.Empty

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

-- The set of naturals is infinite
ℕ-infinite : Infinite ℕ
ℕ-infinite finite = contradiction
  where
    open import Data.Vec
    open import Data.Product
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

-- Any set, isomorphic to a finite one is finite
finite-iso : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A ≅ B → Finite A → Finite B
finite-iso A≅B f = record
  { ℵ = Finite.ℵ f
  ; iso = ≅-trans (≅-sym A≅B) (Finite.iso f)
  }

-- Product of finite set is finite
open import Data.Sum as S
open import Data.Fin hiding (_+_)

open import Relation.Binary.PropositionalEquality as P
import Relation.Binary.EqReasoning as EqR

⊎-finite : ∀ {ℓ₁ ℓ₂} {A₁ : Set ℓ₁} {A₂ : Set ℓ₂} → Finite A₁ → Finite A₂ → Finite (A₁ ⊎ A₂)
⊎-finite f₁ f₂ = record
  { ℵ = ℵ
  ; iso = record
    { to = to
    ; from = from
    ; inverseˡ = inverseˡ
    ; inverseʳ = inverseʳ
    }
  }
  where
    ℵ₁ = Finite.ℵ f₁
    ℵ₂ = Finite.ℵ f₂

    ℵ = ℵ₁ + ℵ₂

    open Iso (+≅⊎-fin ℵ₁ ℵ₂) renaming (from to encode; to to decode; inverseʳ to encode∘decode; inverseˡ to decode∘encode)

    iso₁ = Finite.iso f₁
    iso₂ = Finite.iso f₂

    open Iso iso₁ renaming (to to to₁; from to from₁; inverseˡ to inverseˡ₁; inverseʳ to inverseʳ₁)
    open Iso iso₂ renaming (to to to₂; from to from₂; inverseˡ to inverseˡ₂; inverseʳ to inverseʳ₂)

    to = encode ∘ S.map to₁ to₂
    from = S.map from₁ from₂ ∘ decode

    to∘from : S.map to₁ to₂ ∘ S.map from₁ from₂ ≗ id
    to∘from = [ cong inj₁ ∘ inverseˡ₁ , cong inj₂ ∘ inverseˡ₂ ]

    inverseˡ = begin
                 to ∘ from
               ≈⟨ cong encode ∘ to∘from ∘ decode ⟩
                 encode ∘ decode
               ≈⟨ sym ∘ encode∘decode ⟩
                 id
               ∎ where open EqR (P._→-setoid_ _ _)

    from∘to : id ≗ S.map from₁ from₂ ∘ S.map to₁ to₂
    from∘to = [ cong inj₁ ∘ inverseʳ₁ , cong inj₂ ∘ inverseʳ₂ ]

    inverseʳ = begin
                 id
               ≈⟨ from∘to ⟩
                 S.map from₁ from₂ ∘ S.map to₁ to₂
               ≈⟨ sym ∘ cong (map from₁ from₂) ∘ decode∘encode ∘ (map to₁ to₂) ⟩
                 from ∘ to
               ∎ where open EqR (P._→-setoid_ _ _)
