
{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.One
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Relation.Binary.PropositionalEquality

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

module CCA2 = Game.IND-CCA2 PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec 
module CCA  = Game.IND-CCA  PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec

f : ((Message × Message) × (CipherText → Bit))
  → ((Message × Message) × (CipherText → CCA.DecRound Bit))
f (m , g) = m , (λ c → done (g c))

A-transform : CCA.Adv → CCA2.Adversary
A-transform adv = adv' where
    adv' : _ → _ → _ 
    adv' rₐ pk = mapStrategy f (adv rₐ pk)
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


correct : ∀ {rₐ rₑ rₖ} b adv → CCA.⅁  b adv               (rₐ , rₖ , rₑ)
                             ≡ CCA2.EXP b (A-transform adv) (rₐ , rₖ , rₑ)
correct {rₐ}{rₑ}{rₖ} b adv with KeyGen rₖ
... | pk , sk 
 =  cong (λ x → runStrategy (Dec sk) (proj₂ x (Enc pk (proj (proj₁ x) b) rₑ)))
         (sym (run-map (Dec sk) f (adv rₐ pk)))


  
