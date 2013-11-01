

{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.One
open import Data.Two
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary.PropositionalEquality

import Game.IND-CPA-dagger
import Game.IND-CPA

module Game.Transformation.CPA-CPAd
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

module CPAd = Game.IND-CPA-dagger PubKey SecKey Message CipherText Rₑ Rₖ Rₐ            𝟙 KeyGen Enc
module CPA  = Game.IND-CPA        PubKey SecKey Message CipherText Rₑ Rₖ (𝟚 × Rₑ × Rₐ) 𝟙 KeyGen Enc

A-transform : (adv : CPAd.Adv) → CPA.Adv
A-transform (adv₁ , adv₂) = adv₁' , adv₂'
  where
    adv₁' : ∀ _ _ _ → _
    adv₁' (_ , _ , rₐ) = adv₁ rₐ
  
    adv₂' : ∀ _ _ _ → _
    adv₂' (t , rₑ , rₐ) pk c₀ = adv₂ rₐ pk c₀ (Enc pk (adv₁ rₐ pk t) rₑ)


{-

  If t ≠ b then we (A-transform adv) guess correctly if adv guess correctly

-}

correct : ∀ {rₑ rₑ' rₖ rₐ } b adv
        → CPAd.⅁  b adv             (rₐ , rₖ , rₑ , rₑ' , _)
        ≡ CPA.⅁ b (A-transform adv) ((not b , rₑ' , rₐ) , rₖ , rₑ , _)
correct b adv = refl


-- -}
-- -}
-- -}
-- -}
-- -}
