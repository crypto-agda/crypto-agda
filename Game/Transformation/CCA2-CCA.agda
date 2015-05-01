{-# OPTIONS --without-K --copatterns #-}

open import Type
open import Function
open import Data.Bit
open import Data.Maybe
open import Data.Product.NP
open import Data.One
open import Control.Strategy renaming (run to run-round; map to mapStrategy)
open import Game.Challenge

open import Relation.Binary.PropositionalEquality

open import Crypto.Schemes
import Game.IND-CPA-utils
import Game.IND-CCA
import Game.IND-CCA2

module Game.Transformation.CCA2-CCA
  (pke : Pubkey-encryption)
  -- randomness supply for, adversary, adversary state
  (Rₐ Rₐ' Rₓ : ★)
  
  where

open Pubkey-encryption pke
open Game.IND-CPA-utils Message CipherText

CPA-A-transform : CPAAdversary Bit → CPAAdversary (DecRound Bit)
get-chal (CPA-A-transform A) = get-chal A
put-resp (CPA-A-transform A) = done ∘ put-resp A

module CCA2 = Game.IND-CCA2 pke Rₐ
module CCA  = Game.IND-CCA  pke Rₐ

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
 =  cong (λ A → run-round (dec sk) (put-resp A (enc pk (get-chal A b) rₑ)))
         (sym (run-map (dec sk) CPA-A-transform (adv rₐ pk)))

         where k  = key-gen rₖ
               pk = fst k
               sk = snd k
