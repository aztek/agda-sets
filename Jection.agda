open import Agda.Primitive
open import Relation.Binary.Core
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

module Jection where

-- Injection
record Injective {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor injective-by
  field
    injectivity : ∀ {a₁ a₂} → f a₁ ≡ f a₂ → a₁ ≡ a₂

record LeftInvertible {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor invertibleˡ
  field
    g : B → A
    idˡ : g ∘ f ≗ id

toInjective : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → LeftInvertible f → Injective f
toInjective (invertibleˡ g idˡ) = injective-by (λ e → trans (sym (idˡ _)) (trans (cong g e) (idˡ _)))

--toLeftInvertible : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Injective f → LeftInvertible f
--toLeftInvertible (injective-by i) = {!!} -- does not hold in constructive mathematics

record Injection {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor injection
  field
    {f} : A → B
    injective : Injective f

infix 0 _↣_
_↣_ : ∀ {ℓ₁ ℓ₂} → REL (Set ℓ₁) (Set ℓ₂) (ℓ₁ ⊔ ℓ₂)
A ↣ B = Injection A B

-- Surjection
record Surjective {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor surjective-by
  field
    surjectivity : ∀ b → ∃ λ a → f a ≡ b

record RightInvertible {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor invertibleʳ
  field
    h : B → A
    idʳ : f ∘ h ≗ id

toSurjective : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → RightInvertible f → Surjective f
toSurjective (invertibleʳ h idʳ) = surjective-by (λ b → h b , idʳ b)

toRightInvertible : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Surjective f → RightInvertible f
toRightInvertible (surjective-by s) = invertibleʳ (proj₁ ∘ s) (proj₂ ∘ s)

record Surjection {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor surjection
  field
    {f} : A → B
    surjective : Surjective f

infix 0 _↔_
_↠_ : ∀ {ℓ₁ ℓ₂} → REL (Set ℓ₁) (Set ℓ₂) (ℓ₁ ⊔ ℓ₂)
A ↠ B = Surjection A B

record Bijective {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor bijective-by
  field
    injective  : Injective  f
    surjective : Surjective f

record Bijection {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor bijection
  field
    {f} : A → B
    bijective : Bijective f

infix 0 _↠_
_↔_ : ∀ {ℓ₁ ℓ₂} → REL (Set ℓ₁) (Set ℓ₂) (ℓ₁ ⊔ ℓ₂)
A ↔ B = Bijection A B

open import Function.Equivalence using (_⇔_; module Equivalence)

record Invertible′ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor invertible′
  field
    invˡ : LeftInvertible f
    invʳ : RightInvertible f

--Invertible′⇔Bijective : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Invertible f ⇔ Bijective f
--Invertible′⇔Bijective = ?

--toInvertible′ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Bijective f → Invertible′ f
--toInvertible′ (bijective-by i s) = invertible′ (toLeftInvertible i) (toRightInvertible s)

toBijection : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Invertible′ f → Bijective f
toBijection (invertible′ invˡ invʳ) = bijective-by (toInjective invˡ) (toSurjective invʳ)

record Invertible {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor invertible
  field
    {f⁻¹} : B → A
    idˡ : f⁻¹ ∘ f ≗ id
    idʳ : f ∘ f⁻¹ ≗ id

Invertible′→Invertible : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Invertible′ f → Invertible f
Invertible′→Invertible {f = f} (invertible′ (invertibleˡ g idˡ) (invertibleʳ h idʳ)) = invertible idˡ idʳ′
  where
    same-inverse : g ≗ h
    same-inverse b = trans (sym (cong g (idʳ b))) (idˡ (h b))

    idʳ′ : f ∘ g ≗ id
    idʳ′ b = trans (cong f (same-inverse b)) (idʳ b)

Invertible→Invertible′ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Invertible f → Invertible′ f
Invertible→Invertible′ (invertible {f⁻¹} idˡ idʳ) = invertible′ (invertibleˡ f⁻¹ idˡ) (invertibleʳ f⁻¹ idʳ)


--Invertible⇔Bijective : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Invertible′ f ⇔ Bijective f
--Invertible⇔Bijective = ?

Bijection→Invertible : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Bijective f → Invertible f
Bijection→Invertible = {!!} --Invertible′→Invertible ∘ toInvertible′

Invertible→Bijection : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} → Invertible f → Bijective f
Invertible→Bijection = toBijection ∘ Invertible→Invertible′

Invertible² : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} (i : Invertible f) → Invertible (Invertible.f⁻¹ i) 
Invertible² (invertible idˡ idʳ) = invertible idʳ idˡ

↔-sym : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A ↔ B → B ↔ A
↔-sym (bijection bij) = bijection (Invertible→Bijection (Invertible² (Bijection→Invertible bij)))
