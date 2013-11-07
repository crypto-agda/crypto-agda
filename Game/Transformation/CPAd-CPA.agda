
{-# OPTIONS --without-K --copatterns #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.One
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary.PropositionalEquality

import Game.IND-CPA-dagger
import Game.IND-CPA

module Game.Transformation.CPAd-CPA
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

module CPA† = Game.IND-CPA-dagger PubKey SecKey Message CipherText Rₑ Rₖ Rₐ 𝟙 KeyGen Enc
module CPA  = Game.IND-CPA        PubKey SecKey Message CipherText Rₑ Rₖ Rₐ 𝟙 KeyGen Enc

{-
f : (Message × Message) × (CipherText → DecRound Bit)
  → (Message × Message) × (CipherText → CipherText → DecRound Bit)
f (m , g) = m , λ c _ → g c
-}

R-transform : CPA†.R → CPA.R
R-transform (rₐ , rₖ , rₑ , _ , _) = rₐ , rₖ , rₑ , _

module _ (A : CPA.Adversary) where
  open CPA.Adversary

  A† : CPA†.Adversary
  m  A† = m A
  b′ A† rₐ pk c₀ c₁ = b′ A rₐ pk c₀

  lemma : ∀ b t r
          → CPA.EXP  b   A  (R-transform r)
          ≡ CPA†.EXP b t A† r
  lemma _ _ _ = refl

  -- If we are able to do the transformation, then we get the same advantage
  correct : ∀ b r
            → CPA.EXP  b A          (R-transform r)
            ≡ CPA†.EXP b (not b) A† r
  correct _ _ = refl

-- -}
