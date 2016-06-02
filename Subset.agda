open import Level
open import Relation.Binary.Core

module Subset where

-- Injection
record _↣_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    f : A → B
    injectivity : ∀ a b → f a ≡ f b → a ≡ b

id : ∀ {ℓ} {A : Set ℓ} → A ↣ A
id = record { f = λ x → x ; injectivity = λ _ _ x → x }

-- Subset
data _⊆_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  ⊆-map : A ↣ B → A ⊆ B

--record _⊆_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
--  field
--    map : A ↣ B

⊆-refl : ∀ {ℓ} {A : Set ℓ} → A ⊆ A
⊆-refl = ⊆-map id --record { map = id }

-- Isomorphism
record _≅_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    A⊆B : A ⊆ B
    B⊆A : B ⊆ A

≅-refl : ∀ {ℓ} {A : Set ℓ} → A ≅ A
≅-refl = record { A⊆B = ⊆-refl ; B⊆A = ⊆-refl }

open import Data.Nat hiding (suc; zero)

record Countable {ℓ} (A : Set ℓ) : Set (suc ℓ) where
  field
    B : Set ℓ
    A≅B : A ≅ B
    B⊆ℕ : B ⊆ ℕ

⊆ℕ-countable : ∀ {ℓ} {A : Set ℓ} → A ⊆ ℕ → Countable A
⊆ℕ-countable A⊆ℕ = record { B = _ ; A≅B = ≅-refl ; B⊆ℕ = A⊆ℕ }

open import Data.Fin

countable-fin : ∀ n → Countable (Fin n)
countable-fin n = ⊆ℕ-countable (⊆-map (map n)) --(record { map = map n })
  where
    injectivity : ∀ n a b → toℕ a ≡ toℕ b → a ≡ b
    injectivity ℕ.zero () _ _
    injectivity (ℕ.suc n₁) a b x = {!a!}

    map : ∀ n → Fin n ↣ ℕ
    map n = record { f = toℕ ; injectivity = injectivity n }
