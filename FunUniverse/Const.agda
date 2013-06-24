module FunUniverse.Const where

open import Type
open import Data.Unit using (⊤)

open import FunUniverse.Data
open import FunUniverse.Core

constFuns : ★ → FunUniverse ⊤
constFuns A = ⊤-U , λ _ _ → A

module ConstFunTypes A = FunUniverse (constFuns A)

⊤-FunOps : FunOps (constFuns ⊤)
⊤-FunOps = _
