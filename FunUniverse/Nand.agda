-- http://en.wikipedia.org/wiki/NAND_logic
open import Type
open import FunUniverse.Core
open import Level.NP
--open import FunUniverse.Rewiring

module FunUniverse.Nand {t} {T : ★_ t} {funU : FunUniverse T} (rewiring : Rewiring funU) where

open FunUniverse funU
open Rewiring rewiring

module FromNand (nand : `𝟚 `× `𝟚 `→ `𝟚) where
  not : `𝟚 `→ `𝟚
  not  = dup ⁏ nand 

  and or nor xor xnor : `𝟚 `× `𝟚 `→ `𝟚

  and  = nand ⁏ not
  or   = < not × not > ⁏ nand
  nor  = or ⁏ not
  xor  = < dup × dup > ⁏ inner2 (nand ⁏ dup) ⁏ < nand × nand > ⁏ nand
  xnor = xor ⁏ not

  -- xnor is _==_

  module _ {A B C D E}
    (f : A `× B `→ D)
    (g : A `× C `→ E) where

    dispatch : A `× B `× C `→ D `× E
    dispatch = first dup ⁏ inner2 swap ⁏ < f × g > 

  -- 2-to-1 multiplexer
  -- mux (s , (e₀ , e₁)) = eₛ
  -- or
  -- mux (s , (e₀ , e₁)) = (not s ∧ e₀) ∨ (s ∧ e₁)
  mux : `𝟚 `× (`𝟚 `× `𝟚) `→ `𝟚
  mux = dispatch (< not × id > ⁏ and) and ⁏ or
