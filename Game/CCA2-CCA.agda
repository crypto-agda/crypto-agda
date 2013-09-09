
{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

import Game.IND-CCA
import Game.IND-CCA2

module Game.CCA2-CCA
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ Rₐ' Rₓ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)
  
where

open import Game.CCA-Common
module CCA2 = Game.IND-CCA2 PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₐ' Rₓ KeyGen Enc Dec 
module CCA  = Game.IND-CCA  PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₐ' Rₓ KeyGen Enc Dec

A-transform : CCA.Adv → CCA2.Adv
A-transform (m , d) = m' , d' where
  m' : _ → _ → _
  m' rₐ pk = m rₐ pk

  d' : _ → _ → _ → (_ : _) → _
  d' rₐ' rₓ pk c = Pick (d rₐ' rₓ pk c)
      
valid-transform : ∀ adv → CCA2.Valid-Adv (A-transform adv)
valid-transform adv = tt
  
correct : ∀ {rₑ rₖ rₐ} b adv → CCA.⅁  b adv               (rₐ , rₖ , rₑ)
                             ≡ CCA2.⅁ b (A-transform adv) (rₐ , rₖ , rₑ)
correct 1b adv = refl
correct 0b adv = refl
