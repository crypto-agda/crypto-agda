
open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product

open import Data.Nat.NP
--open import Rat

open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open Operators
open import Control.Strategy renaming (run to runStrategy)
import Game.IND-CPA-utils

open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2-dagger
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

open Game.IND-CPA-utils Message CipherText
open CPAAdversary

Adversary : ★
Adversary = Rₐ → PubKey →
                   DecRound              -- first round of decryption queries
                     (CPAAdversary       -- choosen plaintext attack
                       (CipherText →     -- in which a second ciphertext is provided
                          DecRound Bit)) -- second round of decryption queries

{-
Valid-Adv : Adv → Set
Valid-Adv (m , d) = ∀ {rₐ rₓ pk c c'} → Valid (λ x → x ≢ c × x ≢ c') (d rₐ rₓ pk c c')
-}

R : ★
R = Rₐ × Rₖ × Rₑ × Rₑ

Experiment : ★
Experiment = Adversary → R → Bit

module EXP (b : Bit) (A : Adversary) (rₐ : Rₐ) (pk : PubKey) (sk : SecKey) (rₑ₀ rₑ₁ : Rₑ) where
  decRound = runStrategy (Dec sk)
  cpaA     = decRound (A rₐ pk)
  mb       = proj′ (get-m cpaA)
  c₀       = Enc pk (mb b)       rₑ₀
  c₁       = Enc pk (mb (not b)) rₑ₁
  b′       = decRound (put-c cpaA c₀ c₁)

EXP : Bit → Experiment
EXP b A (rₐ , rₖ , rₑ₀ , rₑ₁) with KeyGen rₖ
... | pk , sk = EXP.b′ b A rₐ pk sk rₑ₀ rₑ₁

module Advantage
  (μₑ : Explore₀ Rₑ)
  (μₖ : Explore₀ Rₖ)
  (μₐ : Explore₀ Rₐ)
  where
  μR : Explore₀ R
  μR = μₐ ×ᵉ μₖ ×ᵉ μₑ ×ᵉ μₑ
  
  module μR = FromExplore₀ μR
  
  run : Bit → Adversary → ℕ
  run b adv = μR.count (EXP b adv)
    
  {-
  Advantage : Adv → ℚ
  Advantage adv = dist (run 0b adv) (run 1b adv) / μR.Card
  -}
