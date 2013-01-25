module isos-examples where

open import Function
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
import Function.Related as FR
open import Type hiding (★)
open import Data.Product.NP
open import Data.Bool
open import Data.Bits
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡

_≈₂_ : ∀ {a} {A : ★ a} (f g : A → Bit) → ★ _
_≈₂_ {A = A} f g = Σ A (T ∘ f) ↔ Σ A (T ∘ g)

module _ {a r} {A : ★ a} {R : ★ r} where
  _≈_ : (f g : A → R) → ★ _
  f ≈ g = ∀ (O : R → ★ r) → Σ A (O ∘ f) ↔ Σ A (O ∘ g)

  ≈-refl : Reflexive {A = A → R} _≈_
  ≈-refl _ = FI.id

  ≈-trans : Transitive {A = A → R} _≈_
  ≈-trans p q O = q O FI.∘ p O

  ≈-sym : Symmetric {A = A → R} _≈_
  ≈-sym p O = FI.sym (p O)

module _ {a b c} {A : ★ a} {B : ★ b} {C : A → ★ c} (f : A ↔ B) where
  private
    left-f = FI.Inverse.left-inverse-of f
    right-f = FI.Inverse.right-inverse-of f
    coe : ∀ x → C x → C (from f (to f x))
    coe x = ≡.subst C (≡.sym (left-f x))
    coe' : (xp : Σ A C) → C (from f (to f (proj₁ xp)))
    coe' (x , p) = coe x p
    ⇒ : Σ A C → Σ B (C ∘ from f)
    ⇒ (x , p) = to f x , coe x p
    ⇐ : Σ B (C ∘ from f) → Σ A C
    ⇐ (x , p) = from f x , p
    left : ∀ x → ⇐ (⇒ x) ≡ x
    left (x , p) rewrite left-f x = refl
    mkΣ≡ : ∀ {a b} {A : ★ a} {x y : A} (B : A → ★ b) {p : B x} {q : B y} (xy : x ≡ y) → subst B xy p ≡ q → (x , p) ≡ (y , q)
    mkΣ≡ _ xy h rewrite xy | h = refl
    right : ∀ x → ⇒ (⇐ x) ≡ x
    right p = mkΣ≡ (C ∘ from f) (right-f (proj₁ p)) (helper p)
            where
                helper : ∀ p → subst (C ∘ from f) (right-f (proj₁ p)) (coe (proj₁ (⇐ p)) (proj₂ (⇐ p))) ≡ proj₂ p
                helper p with to f (from f (proj₁ p)) | right-f (proj₁ p) | left-f (from f (proj₁ p))
                helper _ | ._ | refl | refl = refl
  first-iso : Σ A C ↔ Σ B (C ∘ from f)
  first-iso = inverses (⇒) (⇐) left right

module _ {a b r} {A : ★ a} {B : ★ b} {R : ★ r} where
  _≋_ : (f : A → R) (g : B → R) → ★ _
  f ≋ g = (f ∘ proj₁) ≈ (g ∘ proj₂)

module _ {a b c} {A : ★ a} {B : ★ b} {C : A × B → ★ c} where
  Σ×-swap : Σ (A × B) C ↔ Σ (B × A) (C ∘ swap)
  Σ×-swap = first-iso swap-iso

module _ {a b r} {A : ★ a} {B : ★ b} {R : ★ r} where

  _≋′_ : (f : A → R) (g : B → R) → ★ _
  f ≋′ g = ∀ (O : R → ★ r) →
            (B × Σ A (O ∘ f)) ↔ (A × Σ B (O ∘ g))

  module _ {f : A → R} {g : B → R} where
    open FR.EquationalReasoning

    ≋′→≋ : f ≋′ g → f ≋ g
    ≋′→≋ h O = Σ (A × B) (O ∘ f ∘ proj₁)
             ↔⟨ Σ×-swap ⟩
               Σ (B × A) (O ∘ f ∘ proj₂)
             ↔⟨ Σ-assoc ⟩
               (B × Σ A (O ∘ f))
             ↔⟨ h O ⟩
               (A × Σ B (O ∘ g))
             ↔⟨ FI.sym Σ-assoc ⟩
               Σ (A × B) (O ∘ g ∘ proj₂)
             ∎

    ≋→≋′ : f ≋ g → f ≋′ g
    ≋→≋′ h O = (B × Σ A (O ∘ f))
             ↔⟨ FI.sym Σ-assoc ⟩
               Σ (B × A) (O ∘ f ∘ proj₂)
             ↔⟨ Σ×-swap ⟩
               Σ (A × B) (O ∘ f ∘ proj₁)
             ↔⟨ h O ⟩
               Σ (A × B) (O ∘ g ∘ proj₂)
             ↔⟨ Σ-assoc ⟩
               (A × Σ B (O ∘ g))
             ∎
             -- -}
             -- -}
             -- -}
             -- -}
             -- -}
