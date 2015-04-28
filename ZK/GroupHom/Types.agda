{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_)
open import Algebra.Group
open import Algebra.Group.Homomorphism

module ZK.GroupHom.Types where

record GrpHom (G+ G* : Type)(P : G+ → Type) : Type where
  field
    
    𝔾+ : Group G+
    𝔾* : Group G*

    _==_ : G* → G* → Bool
    ✓-== : ∀ {x y} → x ≡ y → ✓ (x == y)
    ==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y

  open Additive-Group       𝔾+ hiding (_⊗_) public
  open Multiplicative-Group 𝔾* hiding (_^_) public

  field
    φ : G+ → G*
    φ-hom : GroupHomomorphism 𝔾+ 𝔾* φ

    y : G*
    φ⇒P : ∀ x → φ x ≡ y → P x
    P⇒φ : ∀ x → P x → φ x ≡ y
