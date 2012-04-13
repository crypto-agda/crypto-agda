module game where

open import Function.NP
open import Data.Nat.NP
open import Data.Product
open import Data.Bool -- hiding (_≟_)

{-
-- Game
data ⅁ ...
-}

data Strategy (☐_ : Set → Set) (R : Set) : Set₁ where
  say : R → Strategy ☐_ R
  ask : {A : Set} → ☐ A → (A → Strategy ☐_ R) → Strategy ☐_ R

run : ∀ {R} → Strategy id R → R
run (say r)   = r
run (ask a f) = run (f a)

open import Data.Bits

pattern looks-random = 0b
pattern not-random   = 1b

module CryptoGames where

  module CipherGames (M C : Set) where
    SemSecAdv : Set
    SemSecAdv = C → Bit

    CPAAdv : Set
    CPAAdv = ∀ {☐_} (enc : M → ☐ C) → Strategy ☐_ Bit

    data CPAWinner b : Strategy ☐_ Bit → Set where
      win : CPAWinner b (say b)
      ask : CPAWinner b s → CPAWinner b (ask ? (λ ? → ))

  module MACGames (M T : Set) where
    MacAdv : Set
    MacAdv = ∀ {☐_} (mac : M → ☐ T) → Strategy ☐_ (M × T)

    data MACWinner (mac : M → T) : Strategy id (M × T) → Set where
      win : ∀ {m} → MACWinner mac (say (m , mac m))
      ask : ∀ {m f} → MACWinner mac (f (mac m)) → MACWinner mac (ask (mac m) f)
