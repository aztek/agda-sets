open import Level
open import Relation.Binary.Core
open import Data.Product
import Function

module Subset where

-- Injection
data Injective {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  inj : (∀ a b → f a ≡ f b → a ≡ b) → Injective f

record _↣_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    f : A → B
    injectivity : Injective f

-- Surjection
data Surjective {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  sur : (∀ b → ∃ λ a → f a ≡ b) → Surjective f

record _↠_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    f : A → B
    surjectivity : Surjective f

record _↔_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    injective  : A ↣ B
    surjective : A ↠ B

bijection : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B}
            (i : Injective f) (s : Surjective f) → A ↔ B
bijection i s = record
  { injective  = record { f = _ ; injectivity  = i }
  ; surjective = record { f = _ ; surjectivity = s }
  }

↔-sym : 

Injective-id : ∀ {ℓ} {A : Set ℓ} → Injective {A = A} {B = A} Function.id
Injective-id = inj (λ _ _ x → x)

id : ∀ {ℓ} {A : Set ℓ} → A ↣ A
id = record { f = Function.id ; injectivity = Injective-id }

Surjective-id : ∀ {ℓ} {A : Set ℓ} → Surjective {A = A} {B = A} Function.id
Surjective-id = sur (λ b → b , refl)


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
countable-fin n = ⊆ℕ-countable {!!} --(⊆-map (map n)) --(record { map = map n })
  where
    injectivity : ∀ n a b → toℕ a ≡ toℕ b → a ≡ b
    injectivity ℕ.zero () _ _
    injectivity (ℕ.suc n₁) a b x = {!a!}

    --map : ∀ n → Fin n ↣ ℕ
    --map n = record { f = toℕ ; injectivity = injectivity n }

record Finite {ℓ} (A : Set ℓ) : Set (Level.suc ℓ) where
  field
    ℵ : ℕ
    fin : A ≅ Fin ℵ
