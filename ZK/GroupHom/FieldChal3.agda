{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_)
open import Algebra.Field
open import Algebra.Group
open import Algebra.Group.Homomorphism
import ZK.GroupHom.FieldChal2

module ZK.GroupHom.FieldChal3
  {F G : Type}
  (𝔽   : Field F)
  (𝔾   : Group G)
  (open Field 𝔽 hiding (_^_; _⊗_) renaming (+-grp to 𝔽+))

  (_==_ : G → G → Bool)
  (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
  (==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y)

  (_^_ : G → F → G)
  (^-+ : ∀ {b} → GroupHomomorphism 𝔽+ 𝔾 (_^_ b))
  (^-* : ∀ {b x y} → b ^(x * y) ≡ (b ^ x)^ y)
  (^-1 : ∀ {b} → b ^ 1# ≡ b)

  (g y : G)
  where

φ = _^_ g

open ZK.GroupHom.FieldChal2 𝔽 𝔾 _ ✓-== ==-✓
                            _ ^-+ ^-* ^-1
                            φ ^-+ ^-*
                            y
  public
