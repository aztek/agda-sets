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


-- Assuming extensionality, Bool → Bool is finite
import Level as L

Bool→Bool-finite : Extensionality L.zero L.zero → Finite (Bool → Bool)
Bool→Bool-finite extensionality = record
  { ℵ = 4
  ; iso = record
    { to = to
    ; from = from
    ; inverseˡ = inverseˡ
    ; inverseʳ = inverseʳ
    }
  }
  where
    to : (Bool → Bool) → Fin 4
    to f
      with f true | f false
    ...  | true   | true  = zero
    ...  | true   | false = suc zero
    ...  | false  | true  = suc (suc zero)
    ...  | false  | false = suc (suc (suc zero))

    from : Fin 4 → Bool → Bool
    from zero = const true
    from (suc zero) = id
    from (suc (suc zero)) = not
    from (suc (suc (suc zero))) = const false
    from (suc (suc (suc (suc ()))))

    inverseˡ : to ∘ from ≗ id
    inverseˡ zero = refl
    inverseˡ (suc zero) = refl
    inverseˡ (suc (suc zero)) = refl
    inverseˡ (suc (suc (suc zero))) = refl
    inverseˡ (suc (suc (suc (suc ()))))

    inverseʳ : id ≗ from ∘ to
    inverseʳ f = extensionality helper
      where
        true-case : f true ≡ from (to f) true
        true-case
          with f true | f false
        ...  | true   | true  = refl
        ...  | true   | false = refl
        ...  | false  | true  = refl
        ...  | false  | false = refl

        false-case : f false ≡ from (to f) false
        false-case
          with f true | f false
        ...  | true   | true  = refl
        ...  | true   | false = refl
        ...  | false  | true  = refl
        ...  | false  | false = refl

        helper : f ≗ from (to f)
        helper true = true-case
        helper false = false-case


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

-- Maybe of a finite set is finite
open import Data.Maybe

maybe-finite : ∀ {ℓ} {A : Set ℓ} → Finite A → Finite (Maybe A)
maybe-finite finite = record
  { ℵ = suc ℵ
  ; iso = record
    { to = to
    ; from = from
    ; inverseˡ = inverseˡ
    ; inverseʳ = inverseʳ
    }
  }
  where
    open Finite.Finite finite

    to : Maybe _ → Fin (suc ℵ)
    to nothing = zero
    to (just a) = suc (Iso.to iso a)

    from : Fin (suc ℵ) → Maybe _
    from zero = nothing
    from (suc n) = just (Iso.from iso n)

    inverseˡ : to ∘ from ≗ id
    inverseˡ zero = refl
    inverseˡ (suc n) = cong suc (Iso.inverseˡ iso n)

    inverseʳ : id ≗ from ∘ to
    inverseʳ (just a) = cong just (Iso.inverseʳ iso a)
    inverseʳ nothing = refl


-- Product of finite set is finite
open import Data.Sum as S
open import Data.Fin hiding (_+_)

open import Relation.Binary.PropositionalEquality as P
import Relation.Binary.EqReasoning as EqR

⊎-finite : ∀ {ℓ₁ ℓ₂} {A₁ : Set ℓ₁} {A₂ : Set ℓ₂} → Finite A₁ → Finite A₂ → Finite (A₁ ⊎ A₂)
⊎-finite f₁ f₂ = record
  { ℵ = ℵ₁ + ℵ₂
  ; iso = record
    { to = to
    ; from = from
    ; inverseˡ = inverseˡ
    ; inverseʳ = inverseʳ
    }
  }
  where
    open Finite.Finite f₁ renaming (ℵ to ℵ₁; iso to iso₁)
    open Finite.Finite f₂ renaming (ℵ to ℵ₂; iso to iso₂)
    open Iso (+≅⊎-fin ℵ₁ ℵ₂) renaming (from to +-from; to to +-to; inverseˡ to +-inverseˡ; inverseʳ to +-inverseʳ)
    open Iso (⊎-≅ iso₁ iso₂) renaming (from to ⊎-from; to to ⊎-to; inverseˡ to ⊎-inverseˡ; inverseʳ to ⊎-inverseʳ)

    to = +-from ∘ ⊎-to
    from = ⊎-from ∘ +-to

    inverseˡ = begin
                 to ∘ from
               ≈⟨ (λ _ → refl) ⟩
                 +-from ∘ (⊎-to ∘ ⊎-from) ∘ +-to
               ≈⟨ cong +-from ∘ ⊎-inverseˡ ∘ +-to ⟩
                 +-from ∘ +-to
               ≈⟨ sym ∘ +-inverseʳ ⟩
                 id
               ∎ where open EqR (P._→-setoid_ _ _)

    inverseʳ = begin
                 id
               ≈⟨ ⊎-inverseʳ ⟩
                 ⊎-from ∘ ⊎-to
               ≈⟨ sym ∘ cong ⊎-from ∘ +-inverseˡ ∘ ⊎-to ⟩
                 from ∘ to
               ∎ where open EqR (P._→-setoid_ _ _)
