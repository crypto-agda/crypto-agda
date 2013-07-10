{-# OPTIONS --without-K #-}
module FunUniverse.Types where

open import Type hiding (★)
open import Data.Nat.NP using (ℕ)
open import Level.NP
open import Function

open import FunUniverse.Data

record FunUniverse {t} (T : ★ t) : ★ (ₛ t) where
  constructor _,_
  field
    universe : Universe T
    _`→_     : T → T → ★₀

  infix 0 _`→_
  open Universe universe public

  `𝟙→_ : T → ★₀
  `𝟙→ A = `𝟙 `→ A

  `𝟚→_ : T → ★₀
  `𝟚→ A = `𝟚 `→ A

  _`→𝟙 : T → ★₀
  A `→𝟙 = A `→ `𝟙

  _`→𝟚 : T → ★₀
  A `→𝟚 = A `→ `𝟚

  _`→ᵇ_ : ℕ → ℕ → ★₀
  i `→ᵇ o = `Bits i `→ `Bits o

  `Endo : T → ★₀
  `Endo A = A `→ A

module OpFunU {t} {T : Set t} (funU : FunUniverse T) where
  open FunUniverse funU
  opFunU : FunUniverse T
  opFunU = universe , flip _`→_
