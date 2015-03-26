{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Function using (id)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; _≢_; idp; ap; !_; _∙_; module ≡-Reasoning)
open import Algebra.Field
open import Algebra.Group
open import Algebra.Group.Homomorphism
import ZK.GroupHom

module ZK.GroupHom.FieldChal
  {F G+ G* : Type}

  (𝔽  : Field F)
  (𝔾+ : Group G+)
  (𝔾* : Group G*)

  (open Field 𝔽 hiding (_^_; _⊗_))

  (_==_ : G* → G* → Bool)
  (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
  (==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y)

  (_⊗_ : G+ → F → G+)
  (_^_ : G* → F → G*)
  (^-+ : ∀ {b} → GroupHomomorphism +-grp 𝔾* (_^_ b))
  (^-* : ∀ {b x y} → b ^(x * y) ≡ (b ^ x)^ y)
  (^-1 : ∀ {b} → b ^ 1# ≡ b)

  (φ   : G+ → G*)
  (φ-+ : GroupHomomorphism 𝔾+ 𝔾* φ)
  (φ-⊗ : ∀ {x n} → φ (x ⊗ n) ≡ φ x ^ n)

  (y : G*)
  where

open ≡-Reasoning

^-^-1/-id : ∀ {b x y}(x≢y : x ≢ y) → (b ^ (x − y))^((x − y)⁻¹) ≡ b
^-^-1/-id {b} {x} {y} x≢y
  = (b ^(x − y))^((x − y)⁻¹)   ≡⟨ ! ^-* ⟩
    b ^ ((x − y) * (x − y)⁻¹)  ≡⟨ ap (_^_ b) (⁻¹-right-inverse (x−y≢0 x≢y)) ⟩
    b ^ 1#                     ≡⟨ ^-1 ⟩
    b                          ∎

open ZK.GroupHom 𝔾+ 𝔾* _ ✓-== ==-✓ _⊗_ _^_ _−_ id _⁻¹
                 (λ _ → GroupHomomorphism.−-/ ^-+) ^-^-1/-id φ φ-+ φ-⊗ y
               public
-- -}
