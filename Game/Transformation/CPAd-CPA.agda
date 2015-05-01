{-# OPTIONS --without-K --copatterns #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.One
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary.PropositionalEquality

open import Crypto.Schemes
import Game.IND-CPA-dagger
import Game.IND-CPA

module Game.Transformation.CPAd-CPA
  (pke : Pubkey-encryption)
  (Rₐ : Type)
  where

open Pubkey-encryption pke
module CPA† = Game.IND-CPA-dagger pke Rₐ 𝟙
module CPA  = Game.IND-CPA        pke Rₐ 𝟙

R-transform : CPA†.R → CPA.R
R-transform (rₐ , rₖ , rₑ , _ , _) = rₐ , rₖ , rₑ , _

module _ (A : CPA.Adversary) where
  open CPA†.Adversary
  module A = CPA.Adversary A

  A† : CPA†.Adversary
  m  A† = A.m
  b' A† rₐ pk c₀ c₁ = A.b′ rₐ pk c₀

  lemma : ∀ b t r → CPA.EXP b A (R-transform r) ≡ CPA†.EXP b t A† r
  lemma _ _ _ = refl

  -- If we are able to do the transformation, then we get the same advantage
  correct : ∀ b r
            → CPA.EXP  b A          (R-transform r)
            ≡ CPA†.EXP b (not b) A† r
  correct _ _ = refl

-- -}
