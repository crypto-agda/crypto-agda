{-# OPTIONS --without-K #-}
module FunUniverse.Fin where

open import Type
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import FunUniverse.Data
open import FunUniverse.Core

_→ᶠ_ : ℕ → ℕ → ★
_→ᶠ_ i o = Fin i → Fin o

finFunU : FunUniverse ℕ
finFunU = Fin-U , _→ᶠ_

module FinFunUniverse = FunUniverse finFunU
