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

  _`→ᵇ_ : ℕ → ℕ → ★₀
  i `→ᵇ o = `Bits i `→ `Bits o

  `Endo : T → ★₀
  `Endo A = A `→ A

module OpFunU {t} {T : Set t} (funU : FunUniverse T) where
  open FunUniverse funU
  opFunU : FunUniverse T
  opFunU = universe , flip _`→_
