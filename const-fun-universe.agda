module const-fun-universe where

open import Data.Unit using (⊤)

open import data-universe
open import fun-universe

constFuns : Set → FunUniverse ⊤
constFuns A = ⊤-U , λ _ _ → A

module ConstFunTypes A = FunUniverse (constFuns A)

⊤-FunOps : FunOps (constFuns ⊤)
⊤-FunOps = _
