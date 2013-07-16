open import Type
open import FunUniverse.Core

module FunUniverse.Loop where

module LoopType {t} {T : ★_ t} (funU : FunUniverse T) where
  open FunUniverse funU
  Exit? = `𝟚

  record Loop A I B O : ★_ t where
    constructor loop[_⁏_⁏_]
    field
      {S} : T

    Init = A `→ S
    Body = I `× S `→ Exit? `× O `× S
    Exit = S `→ B

    field
      init : Init
      body : Body
      exit : Exit

module Foldl {t} {T : ★_ t} {funU : FunUniverse T}
             (funOps : FunOps funU)
             {I O}
             (z : let open FunUniverse funU in
                  `𝟙 `→ O)
             (f : let open FunUniverse funU in
                  I `× O `→ O) where
    open LoopType funU
    open FunUniverse funU
    open FunOps funOps hiding (foldl)
    foldl : Loop `𝟙 I `𝟙 O
    foldl = loop[ z ⁏ (f ⁏ <tt⁏ <0₂> , dup >) ⁏ tt ]

open import FunUniverse.Agda
open import Data.Product
open import Data.One
open import Data.Two
open import Data.List
open LoopType agdaFunU
open FunOps agdaFunOps hiding (init)

module RunList {A I B O} (loop : Loop A I B O) where

  open Loop loop

  runList₀ : List I × S → List O × S
  runList₁ : List I × Exit? × O × S → List O × S

  runList₁ (is , 0₂ , o , s) = first (_∷_ o) (runList₀ (is , s))
  runList₁ (is , 1₂ , o , s) = (o ∷ [] , s)

  runList₀ ([]     , s) = ([] , s)
  runList₀ (i ∷ is , s) = runList₁ (is , body (i , s))

  runList : List I × A → List O × B
  runList = second init ⁏ runList₀ ⁏ second exit

-- -}
