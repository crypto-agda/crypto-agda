module const-fun-universe where

open import Type
open import Data.Unit using (⊤)

open import data-universe
open import fun-universe

constFuns : ★ → FunUniverse ⊤
constFuns A = ⊤-U , λ _ _ → A

module ConstFunTypes A = FunUniverse (constFuns A)

⊤-FunOps : FunOps (constFuns ⊤)
⊤-FunOps = _
