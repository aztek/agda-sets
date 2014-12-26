open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.EqReasoning as EqR
open import Function

open import Isomorphic

module Isomorphic.Properties (extensionality : ∀ {a b} → Extensionality a b) where

open import Functor (extensionality)
open import BiFunctor (extensionality)

-- Isomorphism is an equivalence relation
≅-refl : ∀ {ℓ} → Reflexive (_≅_ {ℓ})
≅-refl = record
  { to = id
  ; from = id
  ; inverseˡ = λ _ → refl
  ; inverseʳ = λ _ → refl
  }

≅-sym : ∀ {ℓ₁ ℓ₂} → Sym (_≅_ {ℓ₁}) (_≅_ {ℓ₂})
≅-sym A≅B = record
  { to = from
  ; from = to
  ; inverseˡ = sym ∘ inverseʳ
  ; inverseʳ = sym ∘ inverseˡ
  }
  where open Iso A≅B

≅-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} → Trans (_≅_ {ℓ₁} {ℓ₂}) (_≅_ {ℓ₂} {ℓ₃}) (_≅_ {ℓ₁} {ℓ₃})
≅-trans A≅B B≅C = record
  { to = I₂.to ∘ I₁.to
  ; from = I₁.from ∘ I₂.from
  ; inverseˡ = inverseˡ
  ; inverseʳ = inverseʳ
  }
  where
    module I₁ = Iso A≅B
    module I₂ = Iso B≅C

    inverseˡ = begin
                 I₂.to ∘ (I₁.to ∘ I₁.from) ∘ I₂.from
               ≈⟨ cong I₂.to ∘ I₁.inverseˡ ∘ I₂.from ⟩
                 I₂.to ∘ I₂.from
               ≈⟨ I₂.inverseˡ ⟩
                 id
               ∎
               where open EqR (PE._→-setoid_ _ _)

    inverseʳ = begin
                 id
               ≈⟨ I₁.inverseʳ ⟩
                 I₁.from ∘ I₁.to
               ≈⟨ cong I₁.from ∘ I₂.inverseʳ ∘ I₁.to ⟩
                 I₁.from ∘ (I₂.from ∘ I₂.to) ∘ I₁.to
               ∎
               where open EqR (PE._→-setoid_ _ _)

-- A property, involving sums and Fins
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin hiding (_+_)
open import Data.Fin.Props
open import Data.Nat as N hiding (_⊔_)
open import Data.Nat.Properties

+≅⊎-fin : ∀ n m → Fin (n + m) ≅ Fin n ⊎ Fin m
+≅⊎-fin n m = record
  { to = to
  ; from = from
  ; inverseˡ = inverseˡ
  ; inverseʳ = inverseʳ
  }
  where
    -- 0..(n-1) are elements of Fin n
    -- n..(n+m) are elements of Fin m
    from : Fin n ⊎ Fin m → Fin (n + m)
    from (inj₁ n′) = inject+ m n′
    from (inj₂ m′) = raise   n m′

    drop-suc : ∀ {n m} → suc m N.≤ suc n → m N.≤ n
    drop-suc (s≤s m≤n) = m≤n

    to : Fin (n + m) → Fin n ⊎ Fin m
    to i with suc (toℕ i) ≤? n
    ... | yes i<n = inj₁ (fromℕ≤ i<n)
    ... | no  i≮n = inj₂ (reduce≥ i (drop-suc (≰⇒> i≮n)))

    reduce≥-raise : ∀ {n} m {i : Fin n} (i≥m : toℕ (raise m i) N.≥ m) → reduce≥ (raise m i) i≥m ≡ i
    reduce≥-raise zero    _ = refl
    reduce≥-raise (suc m) (s≤s i≥m) = reduce≥-raise m i≥m

    inverseˡ : to ∘ from ≗ id
    inverseˡ (inj₁ i)
      with suc (toℕ (inject+ m i)) ≤? n
    ...  | yes p rewrite sym (inject+-lemma m i) = cong inj₁ (fromℕ≤-toℕ i p)
    ...  | no ¬p = ⊥-elim (¬p lemma)
      where lemma : suc (toℕ (inject+ m i)) N.≤ n
            lemma rewrite sym (inject+-lemma m i) = bounded i
    inverseˡ (inj₂ i)
      with suc (toℕ (raise n i)) ≤? n
    ...  | no ¬p = cong inj₂ (reduce≥-raise n (drop-suc (≰⇒> ¬p)))
    ...  | yes p rewrite toℕ-raise n i = ⊥-elim (lemma p)
      where lemma : ∀ {n m} → suc (n + m) N.≰ n
            lemma {suc n} (s≤s ≤) = lemma ≤

    raise-reduce≥ : ∀ {n} m (i : Fin (m + n)) (i≥m : toℕ i N.≥ m) → i ≡ raise m (reduce≥ i i≥m)
    raise-reduce≥ zero _ _ = refl
    raise-reduce≥ (suc m) zero ()
    raise-reduce≥ (suc m) (suc i) (s≤s i≥m) = cong suc (raise-reduce≥ m i i≥m)

    inverseʳ : id ≗ from ∘ to
    inverseʳ i
      with suc (toℕ i) ≤? n
    ...  | no ¬p = raise-reduce≥ n i (drop-suc (≰⇒> ¬p))
    ...  | yes p = toℕ-injective lemma
      where lemma : toℕ i ≡ toℕ (inject+ m (fromℕ≤ p))
            lemma rewrite sym (inject+-lemma m (fromℕ≤ p)) = sym (toℕ-fromℕ≤ p)

-- Pairwise sums of isomorphic sets are isomorphic
⊎-≅ : ∀ {A B C D} → A ≅ C → B ≅ D → A ⊎ B ≅ C ⊎ D
⊎-≅ = ≅-lift-bifunctor ⊎-bifunctor

-- Pairwise products of isomorphic sets are isomorphic
open import Data.Product using (_×_)

×-≅ : ∀ {A B C D} → A ≅ C → B ≅ D → A × B ≅ C × D
×-≅ = ≅-lift-bifunctor ×-bifunctor
