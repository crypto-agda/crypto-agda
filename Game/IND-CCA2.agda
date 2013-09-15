
{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Unit

open import Data.Nat.NP
open import Rat

open import Explore.Type
open import Explore.Explorable
open import Explore.Product
open Operators
open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2
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
open import Game.CCA-Common Message CipherText
                         
Adv : ★
Adv = Rₐ → PubKey → Strategy ((Message × Message) × (CipherText → Strategy Bit))

{-
Valid-Adv : Adv → Set
Valid-Adv adv = ∀ {rₐ rₓ pk c} → Valid (λ x → x ≢ c) {!!}
-}

R : ★
R = Rₐ × Rₖ × Rₑ

Game : ★
Game = Adv → R → Bit


⅁ : Bit → Game
⅁ b m (rₐ , rₖ , rₑ) with KeyGen rₖ
... | pk , sk = b′ where
  open Eval Dec sk
  
  ev = eval (m rₐ pk)
  mb = proj (proj₁ ev) b
  d = proj₂ ev

  c  = Enc pk mb rₑ
  b′ = eval (d c)

  
module Advantage
  (μₑ : Explore₀ Rₑ)
  (μₖ : Explore₀ Rₖ)
  (μₐ : Explore₀ Rₐ)
  where
  μR : Explore₀ R
  μR = μₐ ×ᵉ μₖ ×ᵉ μₑ
  
  module μR = FromExplore₀ μR
  
  run : Bit → Adv → ℕ
  run b adv = μR.count (⅁ b adv)
  
  Advantage : Adv → ℕ
  Advantage adv = dist (run 0b adv) (run 1b adv)
    
  Advantageℚ : Adv → ℚ
  Advantageℚ adv = Advantage adv / μR.Card
  
-- -}
-- -}
-- -}
-- -}
