
{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Unit

open import Function

open import Relation.Binary.PropositionalEquality

import Game.IND-CCA2-dagger
import Game.IND-CCA2
import Game.IND-CCA

module Game.CCA2-CCA2d
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

module CCA2d = Game.IND-CCA2-dagger PubKey SecKey Message CipherText
    Rₑ Rₖ Rₐ Rₐ' Rₓ KeyGen Enc Dec 
module CCA2 X = Game.IND-CCA2  PubKey SecKey Message CipherText
    Rₑ Rₖ Rₐ (X × Rₐ') Rₓ KeyGen Enc Dec
open import Game.CCA-Common
open Eval

A-transform : (adv : CCA2d.Adv) → CCA2.Adv Bit
A-transform (m , d) = m' , d' where
  m' : _ → _ → _
  m' rₐ pk = m rₐ pk

  d' : _ → _ → _ → (_ : _) → _
  d' (rₜ , rₐ) rₓ pk c = d rₐ rₓ pk c {!!}

correct : ∀ {rₑ rₖ rₐ rₐ' rb} b adv
        → CCA2d.⅁  b adv             (rₐ , rₐ' , rₖ , rₑ , rₑ)
        ≡ CCA2.⅁ Bit b (A-transform adv) (rₐ , (rb , rₐ') , rₖ , rₑ)
correct {rₑ} {rₖ} {rₐ} b (m , d) = {!!}

{-

Need to show that they are valid aswell

-}

valid : ∀ adv → CCA2d.Valid-Adv adv → CCA2.Valid-Adv Bit (A-transform adv)
valid adv valid = {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
