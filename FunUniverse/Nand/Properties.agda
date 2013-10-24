open import Level.NP
open import Type
open import Data.One
open import Data.Two hiding (nand)
open import Data.Product
open import Function.NP
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open import Explore.Core
open import Explore.Properties
import Explore.Explorable
open import Explore.Universe

open import FunUniverse.Nand
open import FunUniverse.Agda

module FunUniverse.Nand.Properties where

module Test {B : ★} (_≟_ : Decidable {A = B} _≡_)
            (A : U)
            {f g : El A → B} where
  module _ {ℓ} where
    Aᵉ : Explore ℓ (El A)
    Aᵉ = exploreU A
    Aⁱ : ExploreInd ℓ Aᵉ
    Aⁱ = exploreU-ind A
  Aˡ : Lookup {₀} Aᵉ
  Aˡ = lookupU A

  Check! = Aᵉ (Lift 𝟙) _×_ λ x → ✓ ⌊ f x ≟ g x ⌋

  check! : {p✓ : Check!} → f ≗ g
  check! {p✓} x = toWitness (Aˡ p✓ x)

  {- Unused
  open Explore.Explorable.Explorable₀ Aⁱ
  test-∧ = big-∧ λ x → ⌊ f x ≟ g x ⌋
  -}

module Test22 where
  nand nand' : 𝟚 × 𝟚 → 𝟚

  nand  (x , y) = not (x ∧ y)
  nand' (x , y) = not x ∨ not y

  module N = FromNand funRewiring nand
  module T = Test Data.Two._≟_

  module UnOp where
    open T 𝟚′

    not-ok : N.not ≗ not
    not-ok = check!

  module BinOp where
    open T (𝟚′ ×′ 𝟚′)

    nand-ok : nand ≗ nand'
    nand-ok = check!

    and-ok : N.and ≗ uncurry _∧_
    and-ok = check!

    or-ok : N.or ≗ uncurry _∨_
    or-ok = check!

    nor-ok : N.nor ≗ (not ∘ uncurry _∨_)
    nor-ok = check!

    xor-ok : N.xor ≗ uncurry _xor_
    xor-ok = check!

    xnor-ok : N.xnor ≗ uncurry _==_
    xnor-ok = check!

  module TriOp where
    open T (𝟚′ ×′ (𝟚′ ×′ 𝟚′))

    mux-ok : N.mux ≗ mux
    mux-ok = check!
