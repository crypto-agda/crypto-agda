{-# OPTIONS --without-K --copatterns #-}
-- Assuming the message space is only one bit the attack can be made even simpler.

open import Function
open import Type using (★)
open import Data.Product
open import Data.Two
open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy
open import Game.Challenge

import Game.IND-CCA2

module Attack.Reencryption.OneBit
  (PubKey SecKey CipherText Rₑ Rₖ : ★)

  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → {-Message-}𝟚 → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → {-Message-}𝟚)
  (Reenc  : PubKey → CipherText → Rₑ → CipherText)
  (Reenc-correct : ∀ rₖ m r₀ r₁ →
                      case KeyGen rₖ of λ
                      { (pk , sk) →
                        Dec sk (Reenc pk (Enc pk m r₀) r₁) ≡ m
                      })
  where

module IND-CCA2 = Game.IND-CCA2 PubKey SecKey 𝟚 CipherText Rₑ Rₖ Rₑ KeyGen Enc Dec
open IND-CCA2

module _ (rₐ : Rₑ) (pk : PubKey) where
    CPA-adversary : CPAAdversary (DecRound 𝟚)
    get-chal CPA-adversary   = id -- equivalent to (0₂ , 1₂)
    put-resp CPA-adversary c = ask (Reenc pk c rₐ) done

adversary : IND-CCA2.Adversary
adversary rₐ pk = done (CPA-adversary rₐ pk)

adversary-always-win : ∀ b r → IND-CCA2.EXP b adversary r ≡ b
adversary-always-win b (rₐ , rₖ , rₑ) = Reenc-correct rₖ b rₑ rₐ
