
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product

open import Data.Nat.NP
--open import Rat

open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open Operators
open import Control.Strategy renaming (run to runStrategy)
open import Game.Challenge
import Game.IND-CPA-utils

import Game.IND-CCA2-dagger.Adversary
import Game.IND-CCA2-dagger.Valid

open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2-dagger.Experiment
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

open Game.IND-CCA2-dagger.Adversary PubKey Message CipherText Rₐ

R : ★
R = Rₐ × Rₖ × Rₑ × Rₑ

Experiment : ★
Experiment = Adversary → R → 𝟚

module EXP (b : 𝟚) (A : Adversary) (rₐ : Rₐ) (pk : PubKey) (sk : SecKey) (rₑ : Rₑ ²) where
  decRound = runStrategy (Dec sk)
  A1       = A rₐ pk
  cpaA     = decRound A1
  m        = get-chal cpaA
  c        = Enc pk ∘ m ∘ flip _xor_ b ˢ rₑ
  A2       = put-resp cpaA c
  b′       = decRound A2

  c₀ = c 0₂
  c₁ = c 1₂
  rₑ₀ = rₑ 0₂
  rₑ₁ = rₑ 1₂

  c₀-spec : c₀ ≡ Enc pk (m b) rₑ₀
  c₀-spec = refl

  c₁-spec : c₁ ≡ Enc pk (m (not b)) rₑ₁
  c₁-spec = refl

EXP : 𝟚 → Experiment
EXP b A (rₐ , rₖ , rₑ₀ , rₑ₁) with KeyGen rₖ
... | pk , sk = EXP.b′ b A rₐ pk sk [0: rₑ₀ 1: rₑ₁ ]
