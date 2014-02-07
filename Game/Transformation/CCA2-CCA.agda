{-# OPTIONS --without-K --copatterns #-}

open import Type
open import Function
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.One
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)
open import Game.Challenge

open import Relation.Binary.PropositionalEquality

import Game.IND-CPA-utils
import Game.IND-CCA
import Game.IND-CCA2

module Game.Transformation.CCA2-CCA
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

open Game.IND-CPA-utils Message CipherText

CPA-A-transform : CPAAdversary Bit → CPAAdversary (DecRound Bit)
get-chal (CPA-A-transform A) = get-chal A
put-resp (CPA-A-transform A) = done ∘ put-resp A

module CCA2 = Game.IND-CCA2 PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec 
module CCA  = Game.IND-CCA  PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec

A-transform : CCA.Adversary → CCA2.Adversary
A-transform adv = adv' where
    adv' : _ → _ → _ 
    adv' rₐ pk = mapStrategy CPA-A-transform (adv rₐ pk)
  {-
  m' : _ → _ → _
  m' rₐ pk = m rₐ pk

  d' : _ → _ → _ → (_ : _) → _
  d' rₐ' rₓ pk c = Pick (d rₐ' rₓ pk c)
  -}

{-
valid-transform : ∀ adv → CCA2.Valid-Adv (A-transform adv)
valid-transform adv = tt
-}

correct : ∀ b adv r → CCA.EXP  b adv               r
                    ≡ CCA2.EXP b (A-transform adv) r
correct b adv (rₐ , rₖ , rₑ)
 =  cong (λ A → runStrategy (Dec sk) (put-resp A (Enc pk (get-chal A b) rₑ)))
         (sym (run-map (Dec sk) CPA-A-transform (adv rₐ pk)))

         where k  = KeyGen rₖ
               pk = proj₁ k
               sk = proj₂ k
