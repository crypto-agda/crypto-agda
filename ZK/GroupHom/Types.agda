{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Type.Eq
open import Relation.Binary.PropositionalEquality.NP using (_≡_)
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import SynGrp

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
    .φ⇒P : ∀ x → φ x ≡ y → P x
    .P⇒φ : ∀ x → P x → φ x ≡ y

record `ZK-hom (`𝔾+ `𝔾* : SynGrp)(P : ElGrp `𝔾+ → Type) : Type where

  G+ : Type
  G+ = ElGrp `𝔾+
  G* : Type
  G* = ElGrp `𝔾*
  𝔾+ : Group G+
  𝔾+ = El𝔾rp `𝔾+
  𝔾* : Group G*
  𝔾* = El𝔾rp `𝔾*
  instance
    G*-eq? = SynGrp-Eq? `𝔾*

  open Eq? G*-eq?
  open Additive-Group       𝔾+ hiding (_⊗_) public
  open Multiplicative-Group 𝔾* hiding (_^_) public

  field
    `φ : SynHom `𝔾+ `𝔾*

  φ = ElHom `φ
  φ-hom = Elℍom `φ

  field
    y : G*
    .φ⇒P : ∀ x → φ x ≡ y → P x
    .P⇒φ : ∀ x → P x → φ x ≡ y

  zk-hom : ZK-hom G+ G* P
  zk-hom = record
             { 𝔾+ = 𝔾+ ; 𝔾* = 𝔾*
             ; φ = φ ; φ-hom = φ-hom
             ; y = y ; φ⇒P = φ⇒P ; P⇒φ = P⇒φ }
-- -}
-- -}
-- -}
-- -}
