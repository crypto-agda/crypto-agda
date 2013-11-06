
{-# OPTIONS --without-K #-}

open import Type
open import Function
open import Data.Bit
open import Data.Two.Equality
open import Data.Maybe
open import Data.Product
open import Data.Unit

open import Data.Nat.NP hiding (_==_)
open import Data.Nat.Distance
--open import Rat

open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open Operators
open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy renaming (run to runStrategy)

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

-- This describes a "round" of decryption queries
DecRound : ★ → ★
DecRound = Strategy CipherText Message

-- This describes the CPA part of CCA
CPAAdversary : ★ → ★
CPAAdversary Next = (Message × Message) × (CipherText → Next)
                         
Adversary : ★
Adversary = Rₐ → PubKey →
                   DecRound           -- first round of decryption queries
                     (CPAAdversary     -- choosen plaintext attack
                       (DecRound Bit)) -- second round of decryption queries

{-
TODO
Valid-Adv : Adv → Set
Valid-Adv adv = ∀ {rₐ rₓ pk c} → Valid (λ x → x ≢ c) {!!}
-}

R : ★
R = Rₐ × Rₖ × Rₑ

EXP : Bit → Adversary → R → Bit
EXP b m (rₐ , rₖ , rₑ) with KeyGen rₖ
... | pk , sk = b′ where
  eval = runStrategy (Dec sk)
  
  ev = eval (m rₐ pk)
  mb = proj (proj₁ ev) b
  d = proj₂ ev

  c  = Enc pk mb rₑ
  b′ = eval (d c)

game : Adversary → (Bit × R) → Bit
game A (b , r) = b == EXP b A r

module Cheating
   (m : Bit → Message)
   (m⁻¹ : Message → Bit)
   where
  cheatingA : Adversary
  cheatingA rₐ pk = done (tabulate₂ m , λ c → ask c (done ∘ m⁻¹))

  module _
    (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                          Dec sk (Enc pk m rₑ) ≡ m)
    (m⁻¹-m : ∀ x → m⁻¹ (m x) ≡ x)
    where

    cheatingA-always-wins : ∀ r → game cheatingA r ≡ 1b
    cheatingA-always-wins (b , rₐ , rₖ , rₑ) =
      ap (_==_ b ∘ m⁻¹) (DecEnc rₖ rₑ (proj (tabulate₂ m) b) ∙ proj-tabulate₂ m b) ∙ ==-≡1₂.reflexive (!(m⁻¹-m b))
  
module Advantage
  (μₑ : Explore₀ Rₑ)
  (μₖ : Explore₀ Rₖ)
  (μₐ : Explore₀ Rₐ)
  where
  μR : Explore₀ R
  μR = μₐ ×ᵉ μₖ ×ᵉ μₑ
  
  module μR = FromExplore₀ μR
  
  run : Bit → Adversary → ℕ
  run b adv = μR.count (EXP b adv)
  
  Advantage : Adversary → ℕ
  Advantage adv = dist (run 0b adv) (run 1b adv)
    
  --Advantageℚ : Adv → ℚ
  --Advantageℚ adv = Advantage adv / μR.Card
  
-- -}
-- -}
-- -}
-- -}
