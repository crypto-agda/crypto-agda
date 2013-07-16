open import Data.Product

module FunUniverse.Nand.Function where

module FromNand {A} (nand : A × A → A) where

    open import FunUniverse.Agda
    open import FunUniverse.Nand (Abstract𝟚.funRewiring A)

    open FromNand nand public

open import Data.Two

module Nand𝟚 = FromNand (uncurry nand)

open import Data.Tree.Binary

module NandTree {A} = FromNand {BinTree A} (uncurry fork)
