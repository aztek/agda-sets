open import Function
open import Data.Fin using (Fin; zero; suc)
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

open import Isomorphic
open import Finite

module Finite.Properties (extensionality : ∀ {a b} → Extensionality a b) where

open import Isomorphic.Properties (extensionality)

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
Bool→Bool-finite : Finite (Bool → Bool)
Bool→Bool-finite = record
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


-- The sum of finite set is finite
open import Data.Sum using (_⊎_)

⊎-finite : ∀ {A B} → Finite A → Finite B → Finite (A ⊎ B)
⊎-finite f₁ f₂ = record
  { ℵ = F₁.ℵ + F₂.ℵ
  ; iso = ≅-trans (⊎-≅ F₁.iso F₂.iso) (≅-sym (+≅⊎-fin F₁.ℵ F₂.ℵ))
  }
  where
    module F₁ = Finite.Finite f₁
    module F₂ = Finite.Finite f₂
