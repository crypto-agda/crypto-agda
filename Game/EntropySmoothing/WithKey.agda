open import Type
open import Data.Bit
open import Data.Bits
open import Data.Product

module Game.EntropySmoothing.WithKey
  (M    : ★)
  (Key  : ★)
  (Hash : ★)
  (ℋ   : Key → M → Hash) -- Hashing function
  (Rₐ   : ★)              -- Adversary randomness
  where

-- Entropy smoothing adversary
Adv : ★
Adv = Rₐ → Key → Hash → Bit

-- The randomness supply needed for the entropy
-- smoothing games
R : ★
R = Key × M × Hash × Rₐ

-- Entropy smoothing game:
--   * input: adversary and randomness supply
--   * output b: adversary claims we are in game ⅁ b
Game : ★
Game = Adv → R → Bit

-- In this game we always use ℋ on a random message
⅁₀ : Game
⅁₀ A (k , m , _ , rₐ) = A rₐ k (ℋ k m)

-- In this game we just retrun a random Hash value
⅁₁ : Game
⅁₁ A (k , _ , h , rₐ) = A rₐ k h

⅁ : Bit → Game
⅁ = proj (⅁₀ , ⅁₁)
