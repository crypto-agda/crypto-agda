
open import Type
open import Function
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

Adversary : ★
Adversary = Rₐ → PubKey →
                   DecRound            -- first round of decryption queries
                     (ChalAdversary    -- choosen plaintext attack (†)
                        (Message ²)    --   the adversary picks two messages
                        (CipherText ²) --   receives the encryption of both of them in a random order
                        (DecRound      -- second round of decryption queries
                           𝟚))         -- the adversary has to guess which message is encrypted as the first ciphertext

{-
Valid-Adv : Adv → Set
Valid-Adv (m , d) = ∀ {rₐ rₓ pk c c'} → Valid (λ x → x ≢ c × x ≢ c') (d rₐ rₓ pk c c')
-}

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

module Advantage
  (μₑ : Explore₀ Rₑ)
  (μₖ : Explore₀ Rₖ)
  (μₐ : Explore₀ Rₐ)
  where
  μR : Explore₀ R
  μR = μₐ ×ᵉ μₖ ×ᵉ μₑ ×ᵉ μₑ
  
  module μR = FromExplore₀ μR
  
  run : 𝟚 → Adversary → ℕ
  run b adv = μR.count (EXP b adv)
    
  {-
  Advantage : Adv → ℚ
  Advantage adv = dist (run 0b adv) (run 1b adv) / μR.Card
  -}
