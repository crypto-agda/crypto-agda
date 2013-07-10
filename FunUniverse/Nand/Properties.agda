open import Level.NP
open import Type
open import Data.Two
open import Data.Product
open import Function.NP
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open import Explore.Type
import Explore.Explorable
open import Explore.Universe

open import FunUniverse.Nand
open import FunUniverse.Agda

module FunUniverse.Nand.Properties where

module Test {B : ★} (_≟_ : Decidable {A = B} _≡_)
            (A : Ty)
            {f g : El A → B} where
  module _ {ℓ} where
    Aᵉ : Explore ℓ (El A)
    Aᵉ = exploreU A
    Aⁱ : ExploreInd ℓ Aᵉ
    Aⁱ = exploreU-ind A
  Aˡ : Lookup {₀} Aᵉ
  Aˡ = lookupU A

  Check! = Aᵉ _×_ λ x → ✓ ⌊ f x ≟ g x ⌋

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

    pf-not : N.not ≗ not
    pf-not = check! 

  module BinOp where
    open T (𝟚′ ×′ 𝟚′)

    pf-nand : nand ≗ nand'
    pf-nand = check!

    pf-and : N.and ≗ uncurry _∧_
    pf-and = check!

    pf-or : N.or ≗ uncurry _∨_
    pf-or = check!

    pf-nor : N.nor ≗ (not ∘ uncurry _∨_)
    pf-nor = check!

    pf-xor : N.xor ≗ uncurry _xor_
    pf-xor = check!

    pf-xnor : N.xnor ≗ uncurry _==_
    pf-xnor = check!

  module TriOp where
    open T (𝟚′ ×′ (𝟚′ ×′ 𝟚′))

    fork : 𝟚 × 𝟚 × 𝟚 → 𝟚
    fork (c , eᵢ) = proj eᵢ c

    pf-fork : N.fork ≗ fork
    pf-fork = check!
