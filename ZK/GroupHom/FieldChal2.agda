{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_)
open import Algebra.Field
open import Algebra.Group
open import Algebra.Group.Homomorphism
import ZK.GroupHom.FieldChal

module ZK.GroupHom.FieldChal2
  {F G   : Type}
  (F-fld : Field F)
  (G-grp : Group G)

  (open Field F-fld hiding (_^_; _⊗_))

  (_==_  : G → G → Bool)
  (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
  (==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y)

  (_^_   : G → F → G)
  (^-hom : ∀ {b} → GroupHomomorphism +-grp G-grp (_^_ b))
  (^-*   : ∀ {b x y} → b ^(x * y) ≡ (b ^ x)^ y)
  (^-1   : ∀ {b} → b ^ 1# ≡ b)

  (φ   : F → G)
  (φ-+ : GroupHomomorphism +-grp G-grp φ)
  (φ-⊗ : ∀ {x n} → φ (x * n) ≡ φ x ^ n)

  (y   : G)
  where

open ZK.GroupHom.FieldChal F-fld +-grp G-grp _ ✓-== ==-✓
                           _ _ ^-hom ^-* ^-1
                           φ φ-+ φ-⊗
                           y
  public
-- -}
