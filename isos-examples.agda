module isos-examples where

open import Function
import Function.Inverse as FI
open FI using (_↔_)
open import Type hiding (★)
open import Data.Product
open import Data.Bool
open import Data.Bits
open import Relation.Binary

_≈₂_ : ∀ {a} {A : ★ a} (f g : A → Bit) → ★ _
_≈₂_ {A = A} f g = Σ A (T ∘ f) ↔ Σ A (T ∘ g)

module _ {a b c} {A : ★ a} {B : ★ b} {C : ★ c} where
  _≈_ : (f : A → C) (g : B → C) → ★ _
  f ≈ g = ∀ (O : C → ★ c) →
            (B × Σ A (O ∘ f)) ↔ (A × Σ B (O ∘ g))

module _ {a c} {A : ★ a} {C : ★ c} where
  ≈-refl : Reflexive {A = A → C} _≈_
  ≈-refl _ = FI.id
