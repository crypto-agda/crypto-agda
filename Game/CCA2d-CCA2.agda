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

module Game.CCA2d-CCA2
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

module CCA2d = Game.IND-CCA2-dagger PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₐ' Rₓ KeyGen Enc Dec 
module CCA2  = Game.IND-CCA2  PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₐ' Rₓ KeyGen Enc Dec

open import Game.CCA-Common

open Eval

A-transform : (adv : CCA2.Adv) → CCA2d.Adv
A-transform (m , d) = m' , d' where
  m' : _ → _ → _
  m' rₐ pk = m rₐ pk

  d' : _ → _ → _ → (_ _ : _) → _
  d' rₐ rₓ pk c c' = d rₐ rₓ pk c

correct : ∀ {rₑ rₖ rₐ rₐ'} b adv
        → CCA2.⅁  b adv               (rₐ , rₐ' , rₖ , rₑ)
        ≡ CCA2d.⅁ b (A-transform adv) (rₐ , rₐ' , rₖ , rₑ , rₑ)
correct {rₑ} {rₖ} {rₐ} b (m , d) = refl

{-

Need to show that they are valid aswell

-}

valid : ∀ adv → CCA2.Valid-Adv adv → CCA2d.Valid-Adv (A-transform adv)
valid adv valid = {!!} -- can't prove this strictly, but it will deviate with
                       -- non-neg probability

-- -}
-- -}
-- -}
-- -}
-- -}
