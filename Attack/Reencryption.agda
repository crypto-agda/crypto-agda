{-# OPTIONS --without-K --copatterns #-}
{-
Any cipher which does supports reencryption (exponential ElGamal, Pailler...) are vulnerable to a CCA2 attack.
-}
open import Function
open import Type using (★)
open import Data.Product
open import Data.Two
open import Data.Maybe
open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy
open import Game.Challenge
open import Crypto.Schemes

import Game.IND-CCA2

module Attack.Reencryption
  (pke : Pubkey-encryption)
  (pkr : Pubkey-reencryption pke)
  (open Pubkey-encryption pke)

  (_==_    : (x y : Message) → 𝟚)
  (m₀ m₁   : Message)
  (m₁==m₁  : m₁ == m₁ ≡ 1₂)
  (¬m₀==m₁ : m₀ == m₁ ≡ 0₂)
  where

open Pubkey-reencryption pkr

m : 𝟚 → Message
m = [0: m₀
     1: m₁ ]

m-diff : ∀ b → m b == m₁ ≡ b
m-diff 1₂ = m₁==m₁
m-diff 0₂ = ¬m₀==m₁

open module IND-CCA2 = Game.IND-CCA2 pke Rₑ

adversary : IND-CCA2.Adversary
adversary rₐ pk = done CPApart
  where CPApart : CPAAdversary _
        get-chal CPApart   = m
        put-resp CPApart c = ask (reenc pk c rₐ) (done ∘ maybe (flip _==_ m₁) 0₂)

adversary-always-win : ∀ b r → IND-CCA2.EXP b adversary r ≡ b
adversary-always-win b (rₐ , rₖ , rₑ) = ap (maybe (flip _==_ m₁) 0₂) (correct-reencryption _ _ _ _) ∙ m-diff b
