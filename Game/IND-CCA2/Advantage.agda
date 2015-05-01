{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Data.Bit
open import Data.Product
open import Data.Zero

open import Data.Nat.NP hiding (_==_)
open import Data.Nat.Distance

open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base

module Game.IND-CCA2.Advantage
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

  open import Game.IND-CCA2 PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec

  Rᵁ = Rₐᵁ ×ᵁ Rₖᵁ ×ᵁ Rₑᵁ

  run : Bit → Adversary → ℕ
  run b adv = count Rᵁ (EXP b adv)

  Advantage : Adversary → ℕ
  Advantage adv = dist (run 0b adv) (run 1b adv)

-- -}
-- -}
-- -}
-- -}
-- -}
