module bintree-proba
  ([0,1] : Set)
where

open import Data.Nat
open import Data.Bits

data Tree : ℕ → Set where
  leaf : ∀ {n} → Bits n → Tree n
  fork : ∀ {n} (proba : [0,1]) (left right : Tree n) → Tree (1 + n)
