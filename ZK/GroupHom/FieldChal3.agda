{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Type.Eq
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
  {{eq?-G : Eq? G}}

  (_^_ : G → F → G)
  (^-+ : ∀ {b} → GroupHomomorphism 𝔽+ 𝔾 (_^_ b))
  (^-* : ∀ {b x y} → b ^(x * y) ≡ (b ^ x)^ y)
  (^-1 : ∀ {b} → b ^ 1# ≡ b)

  (U Y : G)
  where

φ = _^_ U

open ZK.GroupHom.FieldChal2 𝔽 𝔾 {{eq?-G}}
                            _ φ ^-+ ^-*
                            Y ^-+ ^-* ^-1
  public
