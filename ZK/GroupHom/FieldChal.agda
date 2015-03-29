{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Function using (id)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Data.Sum.NP
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

  (φ   : G+ → G*)
  (φ-+ : GroupHomomorphism 𝔾+ 𝔾* φ)
  (φ-⊗ : ∀ {x n} → φ (x ⊗ n) ≡ φ x ^ n)

  (Y : G*)

  (^-+ : GroupHomomorphism +-grp 𝔾* (_^_ Y))
  (^-* : ∀ {a b} → Y ^(a * b) ≡ (Y ^ a)^ b)
  (^-1 : Y ^ 1# ≡ Y)
  where

open ≡-Reasoning

^-^-1/-id : ∀ {c₀ c₁}(c≢ : c₀ ≢ c₁) → (Y ^ (c₀ − c₁))^((c₀ − c₁)⁻¹) ≡ Y
^-^-1/-id {c₀} {c₁} c≢
  = (Y ^ cd)^(cd ⁻¹)  ≡⟨ ! ^-* ⟩
    Y ^ (cd * cd ⁻¹)  ≡⟨ ap (_^_ Y) (⁻¹-right-inverse (x−y≢0 c≢)) ⟩
    Y ^ 1#            ≡⟨ ^-1 ⟩
    Y                 ∎
    where cd = c₀ − c₁

open ZK.GroupHom 𝔾+ 𝔾* _ ✓-== ==-✓ _≢_ inl _⊗_ _^_ _−_ _⁻¹
                 φ φ-+ φ-⊗ Y (λ _ → GroupHomomorphism.−-/ ^-+) ^-^-1/-id
               public
-- -}
