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

  --fork c e0 e1 = (not c ∧ e0) ∨ (c ∧ e1)
  fork : `𝟚 `× `𝟚 `× `𝟚 `→ `𝟚
  fork = dispatch (< not × id > ⁏ and) and ⁏ or
