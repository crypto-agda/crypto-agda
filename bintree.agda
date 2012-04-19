module bintree
  ([0,1] : Set)
where

open import Data.Nat
open import Data.Bits

data T : ℕ → Set where
  leaf : ∀ {n} → Bits n → T n
  fork : ∀ {n} (proba : [0,1]) (left right : T n) → T (1 + n)
