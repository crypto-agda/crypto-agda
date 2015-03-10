
open import Type
open import Function
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product

open import Data.Nat.NP
--open import Rat

open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base
open Operators
open import Control.Strategy renaming (run to runStrategy)
open import Game.Challenge
import Game.IND-CPA-utils

import Game.IND-CCA2-dagger.Adversary
import Game.IND-CCA2-dagger.Valid
import Game.IND-CCA2-dagger.Experiment

open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2-dagger
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑᵁ Rₖᵁ Rₐᵁ : U)
  (let Rₑ = El Rₑᵁ ; Rₖ = El Rₖᵁ ; Rₐ = El Rₐᵁ)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)

  where

open Game.IND-CCA2-dagger.Adversary PubKey Message CipherText Rₐ public

open Game.IND-CCA2-dagger.Valid PubKey Message CipherText Rₐ public
open Game.IND-CCA2-dagger.Experiment PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec public

Rᵁ = Rₐᵁ ×ᵁ Rₖᵁ ×ᵁ Rₑᵁ ×ᵁ Rₑᵁ

run : 𝟚 → Adversary → ℕ
run b adv = count Rᵁ (EXP b adv)

{-
module Advantage
  (μₑ : Explore₀ Rₑ)
  (μₖ : Explore₀ Rₖ)
  (μₐ : Explore₀ Rₐ)
  where
  -- μR : Explore₀ R
  μR = μₐ ×ᵉ μₖ ×ᵉ μₑ ×ᵉ μₑ

  module μR = FromExplore μR

  run : 𝟚 → Adversary → ℕ
  run b adv = μR.count (EXP b adv)

  {-
  Advantage : Adv → ℚ
  Advantage adv = dist (run 0b adv) (run 1b adv) / μR.Card
  -}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
