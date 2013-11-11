{-# OPTIONS --without-K --copatterns #-}

open import Type
open import Data.Maybe
open import Data.Product
open import Data.One
open import Data.Bit
open import Control.Strategy

open import Relation.Binary.PropositionalEquality

import Game.IND-CPA-utils
import Game.IND-CPA
import Game.IND-CCA

module Game.Transformation.CCA-CPA
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
module CCA = Game.IND-CCA PubKey SecKey Message CipherText Rₑ Rₖ Rₐ   KeyGen Enc Dec
module CPA = Game.IND-CPA PubKey SecKey Message CipherText Rₑ Rₖ Rₐ 𝟙 KeyGen Enc

A-transform : CPA.Adversary → CCA.Adversary
A-transform A rₐ pk = done CPApart where
    module A = CPA.Adversary A
    mb = A.m rₐ pk
    CPApart : CPAAdversary _
    get-m CPApart = mb 0b , mb 1b
    put-c CPApart = A.b′ rₐ pk

correct : ∀ {rₑ rₖ rₐ} b adv → CPA.EXP b adv               (rₐ , rₖ , rₑ , _)
                             ≡ CCA.EXP b (A-transform adv) (rₐ , rₖ , rₑ)
correct 1b adv = refl
correct 0b adv = refl
