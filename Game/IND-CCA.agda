{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Control.Strategy renaming (run to runStrategy)

  
module Game.IND-CCA
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)

where

-- This describes a "round" of decryption queries
DecRound : ★ → ★
DecRound = Strategy CipherText Message

-- This describes the CPA part of CCA
CPAAdv : ★
CPAAdv = (Message × Message) × (CipherText → Bit)

Adv : ★
Adv = Rₐ → PubKey → DecRound CPAAdv

R : ★
R = Rₐ × Rₖ × Rₑ

Game : ★
Game = Adv → R → Bit

⅁ : Bit → Game
⅁ b adv (rₐ , rₖ , rₑ) with KeyGen rₖ
... | pk , sk = b′ where
  advCPA = runStrategy (Dec sk) (adv rₐ pk)
  mb = proj (proj₁ advCPA) b
  d = proj₂ advCPA

  c  = Enc pk mb rₑ
  b′ = d c
