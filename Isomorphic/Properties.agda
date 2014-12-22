open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.EqReasoning as EqR
open import Function
open import Isomorphic

module Isomorphic.Properties where

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
  { to = to₂ ∘ to₁
  ; from = from₁ ∘ from₂
  ; inverseˡ = inverseˡ
  ; inverseʳ = inverseʳ
  }
  where
    open Iso A≅B renaming (to to to₁; from to from₁; inverseˡ to inverseˡ₁; inverseʳ to inverseʳ₁)
    open Iso B≅C renaming (to to to₂; from to from₂; inverseˡ to inverseˡ₂; inverseʳ to inverseʳ₂)

    inverseˡ = begin
                 to₂ ∘ (to₁ ∘ from₁) ∘ from₂
               ≈⟨ cong to₂ ∘ inverseˡ₁ ∘ from₂ ⟩
                 to₂ ∘ from₂
               ≈⟨ inverseˡ₂ ⟩
                 id
               ∎
               where open EqR (PE._→-setoid_ _ _)

    inverseʳ = begin
                 id
               ≈⟨ inverseʳ₁ ⟩
                 from₁ ∘ to₁
               ≈⟨ cong from₁ ∘ inverseʳ₂ ∘ to₁ ⟩
                 from₁ ∘ (from₂ ∘ to₂) ∘ to₁
               ∎
               where open EqR (PE._→-setoid_ _ _)

-- A property, involving sums and Fins
open import Data.Sum as S
open import Data.Fin hiding (_+_)
open import Data.Fin.Props
open import Data.Nat as N
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Empty

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
⊎-≅ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      A ≅ C → B ≅ D → A ⊎ B ≅ C ⊎ D
⊎-≅ A≅C B≅D = record
  { to = to
  ; from = from
  ; inverseˡ = inverseˡ
  ; inverseʳ = inverseʳ
  }
  where
    open Iso A≅C renaming (to to to₁; from to from₁; inverseˡ to inverseˡ₁; inverseʳ to inverseʳ₁)
    open Iso B≅D renaming (to to to₂; from to from₂; inverseˡ to inverseˡ₂; inverseʳ to inverseʳ₂)

    to = S.map to₁ to₂
    from = S.map from₁ from₂

    inverseˡ = [ cong inj₁ ∘ inverseˡ₁ , cong inj₂ ∘ inverseˡ₂ ]
    inverseʳ = [ cong inj₁ ∘ inverseʳ₁ , cong inj₂ ∘ inverseʳ₂ ]


-- Pairwise products of isomorphic sets are isomorphic
open import Data.Product as P

×-≅ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      A ≅ C → B ≅ D → A × B ≅ C × D
×-≅ A≅C B≅D = record
  { to = to
  ; from = from
  ; inverseˡ = inverseˡ
  ; inverseʳ = inverseʳ
  }
  where
    open Iso A≅C renaming (to to to₁; from to from₁; inverseˡ to inverseˡ₁; inverseʳ to inverseʳ₁)
    open Iso B≅D renaming (to to to₂; from to from₂; inverseˡ to inverseˡ₂; inverseʳ to inverseʳ₂)

    to = P.map to₁ to₂
    from = P.map from₁ from₂

    inverseˡ : to ∘ from ≗ id
    inverseˡ (a , b) = cong₂ _,_ (inverseˡ₁ a) (inverseˡ₂ b)

    inverseʳ : id ≗ from ∘ to
    inverseʳ (c , d) = cong₂ _,_ (inverseʳ₁ c) (inverseʳ₂ d)


≅-lift : ∀ {a b p} {A : Set a} {B : Set b} {P : ∀ {c} → Set c → Set p}
         (map-to : (A → B) → P A → P B) (map-from : (B → A) → P B → P A) →
         (congˡ : ∀ {to from} → to ∘ from ≗ id → map-to to ∘ map-from from ≗ id) →
         (congʳ : ∀ {to from} → id ≗ from ∘ to → id ≗ map-from from ∘ map-to to) →
         A ≅ B → P A ≅ P B
≅-lift map-to map-from congˡ congʳ A≅B = record
  { to = map-to to
  ; from = map-from from
  ; inverseˡ = congˡ inverseˡ
  ; inverseʳ = congʳ inverseʳ
  }
  where open Iso A≅B
