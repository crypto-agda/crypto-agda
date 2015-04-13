open import Type
open import Data.Zero
open import Data.Two hiding (nand)
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base

open import FunUniverse.Nand
open import FunUniverse.Agda

module FunUniverse.Nand.Properties where

module Test {B : ★} (_≟_ : Decidable {A = B} _≡_)
            (A : U) {f g : El A → B} = CheckDec! A (λ x → f x ≟ g x)

module Test22 where
  nand nand' : 𝟚 × 𝟚 → 𝟚

  nand  (x , y) = not (x ∧ y)
  nand' (x , y) = not x ∨ not y

  module N = FromNand funRewiring nand
  module T = Test Data.Two._≟_

  module UnOp where
    open T 𝟚ᵁ

    not-ok : N.not ≗ not
    not-ok = checkDec!

  module BinOp where
    open T (𝟚ᵁ ×ᵁ 𝟚ᵁ)

    nand-ok : nand ≗ nand'
    nand-ok = checkDec!

    and-ok : N.and ≗ uncurry _∧_
    and-ok = checkDec!

    or-ok : N.or ≗ uncurry _∨_
    or-ok = checkDec!

    nor-ok : N.nor ≗ (not ∘ uncurry _∨_)
    nor-ok = checkDec!

    xor-ok : N.xor ≗ uncurry _xor_
    xor-ok = checkDec!

    xnor-ok : N.xnor ≗ uncurry _==_
    xnor-ok = checkDec!

  module TriOp where
    open T (𝟚ᵁ ×ᵁ (𝟚ᵁ ×ᵁ 𝟚ᵁ))

    mux-ok : N.mux ≗ mux
    mux-ok = checkDec!
-- -}
