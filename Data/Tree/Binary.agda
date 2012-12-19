open import Type hiding (★)

module Data.Tree.Binary where

data BinTree {a} (A : ★ a) : ★ a where
  leaf : A → BinTree A
  fork : (ℓ r : BinTree A) → BinTree A
