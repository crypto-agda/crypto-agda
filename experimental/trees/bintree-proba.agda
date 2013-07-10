{-# OPTIONS --without-K #-}
open import Type
open import Data.Nat
open import Data.Bits

module bintree-proba
  ([0,1] : ★)
where

data Tree : ℕ → ★ where
  leaf : ∀ {n} → Bits n → Tree n
  fork : ∀ {n} (proba : [0,1]) (left right : Tree n) → Tree (1 + n)
