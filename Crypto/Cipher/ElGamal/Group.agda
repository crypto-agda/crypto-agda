{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.NP
              using (_≡_; ap; _∙_)
import Crypto.Cipher.ElGamal.Generic
open import Algebra.Group

-- Note that Message and Blinded could be made equal
-- to G. Because the code does not require it we keep
-- the most flexible version.
module Crypto.Cipher.ElGamal.Group
  -- The type of exponenents (the name Zq, is only suggestive)
  {Zq : Type}
  (ℤq : Group Zq)

  -- The type of the base cyclic group
  {G  : Type}
  (𝔾  : Group G)

  -- The generator element
  (g  : G)

  -- Exponentation
  (_^_ : G → Zq → G)
  (^-comm : ∀ {α x y} → (α ^ x)^ y ≡ (α ^ y)^ x)
  where

open Multiplicative-Group 𝔾 hiding (_^_)

open Crypto.Cipher.ElGamal.Generic G G Zq G g _^_ _*_ _/′_ public

open Functional-correctness /′-* ^-comm public
