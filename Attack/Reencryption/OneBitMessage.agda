-- Assuming the message space is only one bit the attack can be made even simpler.

open import Function
open import Type using (★)
open import Data.Product
open import Data.Two
open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy

import Game.IND-CCA2

module Attack.Reencryption.OneBitMessage
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

adv : IND-CCA2.Adv
adv rₐ pk = done ((0₂ , 1₂) , λ c → ask (Reenc pk c rₐ) λ m′ → done m′)

adv-always-win : ∀ b r → IND-CCA2.⅁ b adv r ≡ b
adv-always-win b (rₐ , rₖ , rₑ) rewrite η-[0:1:] id b = Reenc-correct rₖ b rₑ rₐ
