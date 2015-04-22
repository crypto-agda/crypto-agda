{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Function using (flip)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum.NP
open import Data.Zero
open import Data.Fin.NP using (Fin▹ℕ)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP using (_≡_; _≢_; idp; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Data.Nat.NP hiding (_==_; _^_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties
open import Data.Nat.Primality
open import Data.Nat.DivMod.NP
import Data.Nat.ModInv
import ZK.SigmaProtocol.KnownStatement
import ZK.GroupHom
open import ZK.GroupHom.NumChal

module ZK.GroupHom.NatChal
  (G+ G* : Type)
  (𝔾+ : Group G+)
  (𝔾* : Group G*)
  (_==_ : G* → G* → Bool)
  (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
  (==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y)
  (φ : G+ → G*)
  (φ-hom : GroupHomomorphism 𝔾+ 𝔾* φ)
  (Y : G*)

  (q : ℕ)
  (q-prime : Prime q)

  (open Multiplicative-Group 𝔾*)

  -- Can be turned into a dynamic test!
  (G*-order : Y ^⁺ q ≡ 1#)

  (open Data.Nat.ModInv q q-prime)
  (missing : (x : ℕ) → x ≢ 0 → (1/ x *ℕ x) modℕ q ≡ 1)
  where

open Additive-Group 𝔾+
module φ = GroupHomomorphism φ-hom
module 𝔾* = Group 𝔾*

help! : ∀ x y → y < x → x ∸ y ≢ 0
help! ._ .0 (s≤s z≤n) ()
help! ._ ._ (s≤s (s≤s p)) x = help! _ _ (s≤s p) x
              
ℕ-package : Package
ℕ-package = record
              { Num = ℕ
              ; Prime = Prime
              ; _<_ = _<_
              ; 0ⁿ = 0
              ; 1ⁿ = 1
              ; <-∸≢0 = help!
              ; _+ⁿ_ = _+ℕ_
              ; _∸ⁿ_ = _∸_
              ; _*ⁿ_ = _*ℕ_
              ; compare = ℕcmp.compare
              ; G+ = G+
              ; G* = G*
              ; 𝔾+ = 𝔾+
              ; 𝔾* = 𝔾*
              ; _==_ = _==_
              ; ✓-== = ✓-==
              ; ==-✓ = ==-✓
              ; _⊗ⁿ_ = _⊗⁺_
              ; _^ⁿ_ = _^⁺_
              ; 1^ⁿ = 1^⁺
              ; φ = φ
              ; φ-hom = φ-hom
              ; φ-hom-iterated = λ {_}{x} → φ.hom-iterated⁺ x
              ; q = q
              ; q-prime = q-prime
              ; _div-q = λ x → x div q
              ; _mod-q = λ x → x modℕ q
              ; div-mod-q-propⁿ = λ x → divModPropℕ x q
              ; inv-mod-q = 1/
              ; inv-mod-q-prop = missing
              ; Y = Y
              ; G*-order = G*-order
              ; ^ⁿ1ⁿ+ⁿ = idp
              ; ^ⁿ-* = λ {x} {y} → 𝔾*.^⁺-* y {x} {Y}
              ; ^ⁿ-∸ⁿ = λ {x} {y} y<x → 𝔾*.^⁺-∸ {Y} {x} {y} (≤-pred (≤-step y<x))
              }

open FromPackage ℕ-package public
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
