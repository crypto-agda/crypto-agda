{-# OPTIONS --without-K --copatterns #-}
{-
Any cipher which does supports reencryption (exponential ElGamal, Pailler...) are vulnerable to a CCA2 attack.
-}
open import Function
open import Type using (★)
open import Data.Product
open import Data.Two
open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy
open import Game.Challenge

import Game.IND-CCA2

module Attack.Reencryption
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation
  (Rₑ Rₖ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)
  (Reenc  : PubKey → CipherText → Rₑ → CipherText)
  (Reenc-correct : ∀ rₖ m r₀ r₁ →
                      case KeyGen rₖ of λ
                      { (pk , sk) →
                        Dec sk (Reenc pk (Enc pk m r₀) r₁) ≡ m
                      })

  (_==_    : (x y : Message) → 𝟚)
  (m₀ m₁   : Message)
  (m₁==m₁  : m₁ == m₁ ≡ 1₂)
  (¬m₀==m₁ : m₀ == m₁ ≡ 0₂)
  where

m : 𝟚 → Message
m = [0: m₀
     1: m₁ ]

m-diff : ∀ b → m b == m₁ ≡ b
m-diff 1₂ = m₁==m₁
m-diff 0₂ = ¬m₀==m₁

module IND-CCA2 = Game.IND-CCA2 PubKey SecKey Message CipherText Rₑ Rₖ Rₑ KeyGen Enc Dec
open IND-CCA2

adversary : IND-CCA2.Adversary
adversary rₐ pk = done CPApart
  where CPApart : CPAAdversary _
        get-chal CPApart   = m
        put-resp CPApart c = ask (Reenc pk c rₐ) λ m′ → done (m′ == m₁)

adversary-always-win : ∀ b r → IND-CCA2.EXP b adversary r ≡ b
adversary-always-win b (rₐ , rₖ , rₑ) = ap (flip _==_ m₁) (Reenc-correct rₖ (m b) rₑ rₐ) ∙ m-diff b
