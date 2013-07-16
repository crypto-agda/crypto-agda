{-# OPTIONS --without-K #-}
module FunUniverse.Fin where

open import Type
open import Function
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import FunUniverse.Data
open import FunUniverse.Core
open import FunUniverse.Category
open import FunUniverse.Rewiring.Linear

_→ᶠ_ : ℕ → ℕ → ★
_→ᶠ_ i o = Fin i → Fin o

finFunU : FunUniverse ℕ
finFunU = Fin-U , _→ᶠ_

module FinFunUniverse = FunUniverse finFunU

finCat : Category _→ᶠ_
finCat = id , _∘′_

{-
finLin : LinRewiring finFunU
finLin = mk finCat {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
-}
