{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Type.Eq
open import Relation.Binary.PropositionalEquality.NP using (_≡_)
open import Algebra.Group
open import Algebra.Group.Homomorphism

module ZK.GroupHom.Types where

-- P is the "valid witness" predicate.
record ZK-hom (G+ G* : Type)(P : G+ → Type) : Type where
  field
    
    𝔾+ : Group G+
    𝔾* : Group G*

    {{G*-eq?}} : Eq? G*

  open Eq? G*-eq?
  open Additive-Group       𝔾+ hiding (_⊗_) public
  open Multiplicative-Group 𝔾* hiding (_^_) public

  field
    φ : G+ → G*
    φ-hom : GroupHomomorphism 𝔾+ 𝔾* φ

    y : G*
    φ⇒P : ∀ x → φ x ≡ y → P x
    P⇒φ : ∀ x → P x → φ x ≡ y
-- -}
-- -}
-- -}
-- -}
