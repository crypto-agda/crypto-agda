{-# OPTIONS --without-K #-}
open import Type
open import Data.Two
open import Data.Product

module Game.EntropySmoothing
  (M    : ★)        -- Message
  (Hash : ★)
  (ℋ   : M → Hash) -- Hashing function
  (Rₐ   : ★)        -- Adversary randomness
  where

-- Entropy smoothing adversary
Adversary : ★
Adversary = Rₐ → Hash → 𝟚

-- The randomness supply needed for the entropy
-- smoothing games
R : ★
R = M × Hash × Rₐ

-- Entropy smoothing experiment:
--   * input: adversary and randomness supply
--   * output b: adversary claims we are in game EXP b
Experiment : ★
Experiment = Adversary → R → 𝟚

-- In this game we always use ℋ on a random message
EXP₀ : Experiment
EXP₀ A (m , _ , rₐ) = A rₐ (ℋ m)

-- In this game we just retrun a random Hash value
EXP₁ : Experiment
EXP₁ A (_ , h , rₐ) = A rₐ h

-- Package the two previous games
EXP : 𝟚 → Experiment
EXP = proj (EXP₀ , EXP₁)

game : Adversary → 𝟚 × R → 𝟚
game A (b , r) = EXP b A r
