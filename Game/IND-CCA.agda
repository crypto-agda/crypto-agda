{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
import Game.CCA-Common as Com

  
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

open Com Message CipherText

Adv : ★
Adv = Rₐ → PubKey → Strategy ((Message × Message) × (CipherText → Bit))

R : ★
R = Rₐ × Rₖ × Rₑ

Game : ★
Game = Adv → R → Bit

⅁ : Bit → Game
⅁ b adv (rₐ , rₖ , rₑ) with KeyGen rₖ
... | pk , sk = b′ where
  open Eval Dec sk
  ev = eval (adv rₐ pk)
  mb = proj (proj₁ ev) b
  d = proj₂ ev

  c  = Enc pk mb rₑ
  b′ = d c



