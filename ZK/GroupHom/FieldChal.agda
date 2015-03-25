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
  (F G+ G* : Type)
  (fld-F   : Field F)
  (grp-G+  : Group G+)
  (grp-G*  : Group G*)
  (φ : G+ → G*)
  (y : G*)
  (_==_ : G* → G* → Bool)
  (_^_ : G* → F → G*)
  (_⊗_ : G+ → F → G+)
  where

open ≡-Reasoning

open Field fld-F hiding (_^_; _⊗_)

open ZK.GroupHom grp-G+ grp-G* φ y _==_ _^_ _⊗_ _−_ id _⁻¹ public

module Prfs
  (^-hom : ∀ b → GroupHomomorphism +-grp grp-G* (_^_ b))
  (φ-hom : GroupHomomorphism grp-G+ grp-G* φ)
  (φ-hom-iterated : ∀ {x} n → φ (x ⊗ n) ≡ φ x ^ n)
  (^-* : ∀ {b x y} → b ^ (x * y) ≡ (b ^ x)^ y)
  (^-1 : ∀ {b} → b ^ 1# ≡ b)
  (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
  (==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y)
  where

  ^-^-1/-id : ∀ {b x y}(x≢y : x ≢ y) → (b ^ (x − y))^((x − y)⁻¹) ≡ b
  ^-^-1/-id {b} {x} {y} x≢y
    = (b ^(x − y))^((x − y)⁻¹)   ≡⟨ ! ^-* ⟩
      b ^ ((x − y) * (x − y)⁻¹)  ≡⟨ ap (_^_ b) (⁻¹-right-inverse x−y≢0) ⟩
      b ^ 1#                     ≡⟨ ^-1 ⟩
      b                          ∎
   where
     x−y≢0 : x − y ≢ 0#
     x−y≢0 x−y≡0 = x≢y (cancels-+-right (x−y≡0 ∙ ! 0−-right-inverse))

  module ^-Hom {b} = GroupHomomorphism (^-hom b)

  open Proofs ✓-== ==-✓ φ-hom
       (λ {x} {n} → φ-hom-iterated {x} n)
       (λ {x}{y}{z}_ → ^-Hom.−-/ {x}{y}{z})
       (λ {x}{c} → ^-^-1/-id {x} {c})
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
