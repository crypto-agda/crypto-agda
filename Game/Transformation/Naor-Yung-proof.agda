{-# OPTIONS --without-K #-}
open import Type
open import Data.Two
open import Data.Maybe
open import Data.Product.NP
open import Data.One
open import Relation.Binary.PropositionalEquality

open import Control.Strategy

open import Crypto.Schemes
open import Game.Challenge
import Game.IND-CPA-alt
import Game.IND-CCA
import Game.Transformation.Naor-Yung
import Game.IND-CPA-utils

module Game.Transformation.Naor-Yung-proof
  (pke : Pubkey-encryption)
  (pok : PoK-message-equality-enc pke)
  (open Pubkey-encryption pke)
  (open PoK-message-equality-enc pok)
  (Rₐ  : Type)
  (sim : CipherText ² → Proof)
  where

module NY = Game.Transformation.Naor-Yung pke pok
module ny = Pubkey-encryption NY.NY-encryption

module CPA = Game.IND-CPA-alt pke (𝟚 × Rₖ × Rₑ × Rₐ)
module CCA = Game.IND-CCA NY.NY-encryption Rₐ

open Game.IND-CPA-utils ny.Message ny.CipherText
open ChalAdversary

swap? : ∀ {X : ★} → 𝟚 → (X × X) → 𝟚 → X
swap? b p i = proj′ p (b xor i)

transformation : CCA.Adversary → CPA.Adv
transformation adv (b' , rₖ , rₑ , rₐ) y = go (adv rₐ pk')
  module transformation where

    y' = fst (key-gen rₖ)
    x' = snd (key-gen rₖ)

    pk' = swap? b' (y , y')

    go : DecRound (CPAAdversary 𝟚) → Message ² × (CipherText → 𝟚)
    go (ask (cc , π) x₁) = go (x₁ m?)
      module go-ask where
        m? = [0: nothing 1: dec x' (cc (not b')) ]′ (verify cc π)
    go (done k) = mb , cont
      module go-pick where
        mb = get-chal k
        cont : _ → 𝟚
        cont c = put-resp k (cc' , sim cc')
          module cont where
            cc' = swap? b' (c , enc y' (mb b') rₑ)


R = CPA.R × CCA.R

{-
thm : ∀ adv cpaR ccaR b → CCA.EXP b adv ccaR ≡ CPA.EXP b (transformation adv) cpaR
thm adv cpaR ccaR 1₂ = {!!}
thm adv cpaR ccaR 0₂ = {!!}
-- -}
-- -}
-- -}
-- -}
