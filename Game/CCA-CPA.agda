{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

import Game.IND-CPA
import Game.IND-CCA

module Game.CCA-CPA
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

module CCA = Game.IND-CCA PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₐ KeyGen Enc Dec 
module CPA = Game.IND-CPA PubKey SecKey Message CipherText Rₑ Rₖ Rₐ ⊤  KeyGen Enc 

A-transform : CPA.Adv → CCA.Adv
A-transform (m , d) = m' , d where
  m' : _ → _ → _
  m' rₐ pk = CCA.Pick (mb 0b) (mb 1b) rₐ
    where
      mb = m rₐ pk
      
correct : ∀ {rₑ rₖ rₐ} b adv → CPA.⅁ b adv               (rₐ , rₖ , rₑ , tt)
                             ≡ CCA.⅁ b (A-transform adv) (rₐ , rₖ , rₑ)
correct 1b adv = refl
correct 0b adv = refl
