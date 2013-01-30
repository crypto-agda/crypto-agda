module isos-examples where

open import Function
open import Function.Related.TypeIsomorphisms.NP
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
import Function.Related as FR
open import Type hiding (★)
open import Data.Product.NP
open import Data.Bool.NP using (✓)
open import Data.Unit using (⊤)
open import Data.Bits
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; subst)

_≈₂_ : ∀ {a} {A : ★ a} (f g : A → Bit) → ★ _
_≈₂_ {A = A} f g = Σ A (✓ ∘ f) ↔ Σ A (✓ ∘ g)

module _ {a r} {A : ★ a} {R : ★ r} where
  _≈_ : (f g : A → R) → ★ _
  f ≈ g = ∀ (O : R → ★ r) → Σ A (O ∘ f) ↔ Σ A (O ∘ g)

  ≈-refl : Reflexive {A = A → R} _≈_
  ≈-refl _ = FI.id

  ≈-trans : Transitive {A = A → R} _≈_
  ≈-trans p q O = q O FI.∘ p O

  ≈-sym : Symmetric {A = A → R} _≈_
  ≈-sym p O = FI.sym (p O)

module _ {a r} {A : ★ a} {R : ★ r} (f : A → R) (p : A ↔ A) where
  stable : f ≈ (f ∘ from p)
  stable _ = first-iso p

  stable′ : f ≈ (f ∘ to p)
  stable′ _ = first-iso (FI.sym p)

module _ {a b r} {A : ★ a} {B : ★ b} {R : ★ r} where
  _≋_ : (f : A → R) (g : B → R) → ★ _
  f ≋ g = (f ∘ proj₁) ≈ (g ∘ proj₂)

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
