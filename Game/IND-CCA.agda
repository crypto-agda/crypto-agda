{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Control.Strategy renaming (run to runStrategy)
open import Game.Challenge
import Game.IND-CPA-utils
  
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

open Game.IND-CPA-utils Message CipherText

Adversary : ★
Adversary = Rₐ → PubKey → DecRound (CPAAdversary Bit)

R : ★
R = Rₐ × Rₖ × Rₑ

Experiment : ★
Experiment = Adversary → R → Bit

EXP : Bit → Experiment
EXP b A (rₐ , rₖ , rₑ) with KeyGen rₖ
... | pk , sk = b′ where
  A' = runStrategy (Dec sk) (A rₐ pk)
  m  = get-chal A'
  c  = Enc pk (m b) rₑ
  b′ = put-resp A' c
