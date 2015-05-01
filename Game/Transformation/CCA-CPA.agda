{-# OPTIONS --without-K --copatterns #-}

open import Type
open import Data.Product
open import Data.One
open import Data.Two
open import Control.Strategy
open import Game.Challenge
open import Relation.Binary.PropositionalEquality

open import Crypto.Schemes
import Game.IND-CPA-utils
import Game.IND-CPA
import Game.IND-CCA

module Game.Transformation.CCA-CPA
  (pke : Pubkey-encryption)
  (Rₐ : Type)
  where

open Pubkey-encryption pke
open Game.IND-CPA-utils Message CipherText
module CCA = Game.IND-CCA pke Rₐ
module CPA = Game.IND-CPA pke Rₐ 𝟙

A-transform : CPA.Adversary → CCA.Adversary
A-transform A rₐ pk = done CPApart where
    module A = CPA.Adversary A
    mb = A.m rₐ pk
    CPApart : CPAAdversary _
    get-chal CPApart = mb
    put-resp CPApart = A.b′ rₐ pk

correct : ∀ {rₑ rₖ rₐ} b adv → CPA.EXP b adv               (rₐ , rₖ , rₑ , _)
                             ≡ CCA.EXP b (A-transform adv) (rₐ , rₖ , rₑ)
correct 0₂ adv = refl
correct 1₂ adv = refl
