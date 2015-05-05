{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Type.Eq
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_)
open import Algebra.Field
open import Algebra.Group
open import Algebra.Group.Homomorphism
import ZK.GroupHom.FieldChal

module ZK.GroupHom.FieldChal2
  {F G : Type}
  (𝔽   : Field F)
  (𝔾   : Group G)

  (open Field 𝔽 hiding (_^_; _⊗_) renaming (+-grp to 𝔽+))

  {{eq?-G : Eq? G}}

  (_^_ : G → F → G)

  (φ   : F → G)
  (φ-+ : GroupHomomorphism 𝔽+ 𝔾 φ)
  (φ-⊗ : ∀ {x n} → φ (x * n) ≡ φ x ^ n)

  (Y : G)

  (^-+ : GroupHomomorphism 𝔽+ 𝔾 (_^_ Y))
  (^-* : ∀ {a b} → Y ^(a * b) ≡ (Y ^ a)^ b)
  (^-1 : Y ^ 1# ≡ Y)
  where

open ZK.GroupHom.FieldChal 𝔽 𝔽+ 𝔾 {{eq?-G}}
                           _ _^_ φ φ-+ φ-⊗
                           Y ^-+ ^-* ^-1
  public
-- -}
