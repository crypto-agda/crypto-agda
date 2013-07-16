open import Type
open import Data.Two renaming (mux to mux₂)
open import Data.Product
open import Data.Nat.NP using (ℕ)
open import Data.Vec.NP using ([]; _∷_)

module Language.Simple.Two.Mux where

open import Language.Simple.Interface

data Op : ℕ → ★ where
  mux   : Op 3
  0₂ 1₂ : Op 0

evalOp : EvalOp Op 𝟚
evalOp mux (x ∷ y ∷ z ∷ []) = mux₂ (x , y , z)
evalOp 0₂  []               = 0₂
evalOp 1₂  []               = 1₂

open import Language.Simple.Abstract Op public

lang : Lang Op 𝟚 E
lang = WithEvalOp.lang evalOp
