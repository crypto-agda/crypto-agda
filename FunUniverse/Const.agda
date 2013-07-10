{-# OPTIONS --without-K #-}
module FunUniverse.Const where

open import Type
open import Data.Unit using (⊤)

open import FunUniverse.Data
open import FunUniverse.Core

constFuns : ★ → FunUniverse ⊤
constFuns A = 𝟙-U , λ _ _ → A

module ConstFunTypes A = FunUniverse (constFuns A)

𝟙-FunOps : FunOps (constFuns ⊤)
𝟙-FunOps = _
