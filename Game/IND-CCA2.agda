{-# OPTIONS --without-K --copatterns #-}

open import Type
open import Function
open import Data.Bit
open import Data.Two.Equality
open import Data.Maybe
open import Data.Product
open import Data.Unit
open import Data.Zero

open import Data.Nat.NP hiding (_==_)
open import Data.Nat.Distance
--open import Rat

open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base
open Operators
open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy renaming (run to runStrategy)

open import Game.Challenge
import Game.IND-CPA-utils
import Game.IND-CCA

module Game.IND-CCA2
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑᵁ Rₖᵁ Rₐᵁ : U)
  (let Rₑ = El Rₑᵁ ; Rₖ = El Rₖᵁ ; Rₐ = El Rₐᵁ)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)

  where

module CCA = Game.IND-CCA  PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec
open Game.IND-CPA-utils Message CipherText public

Adversary : ★
Adversary = Rₐ → PubKey →
                   DecRound            -- first round of decryption queries
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
EXP b A (rₐ , rₖ , rₑ) with KeyGen rₖ
... | pk , sk = b′ where
  decRound = runStrategy (Dec sk)

  round1 = decRound (A rₐ pk)
  m      = get-chal round1
  c      = Enc pk (m b) rₑ
  round2 = put-resp round1 c
  b′     = decRound round2

game : Adversary → (Bit × R) → Bit
game A (b , r) = b == EXP b A r

module Cheating
   (m : Message ²)
   (m⁻¹ : Message → Bit)
   where

  cheatingA : Adversary
  cheatingA rₐ pk = done CPApart
    where CPApart : CPAAdversary _
          get-chal CPApart   = m
          put-resp CPApart c = ask c (done ∘ m⁻¹)

  module _
    (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                          Dec sk (Enc pk m rₑ) ≡ m)
    (m⁻¹-m : ∀ x → m⁻¹ (m x) ≡ x)
    where

    cheatingA-always-wins : ∀ r → game cheatingA r ≡ 1b
    cheatingA-always-wins (b , rₐ , rₖ , rₑ) =
      ap (_==_ b ∘ m⁻¹) (DecEnc rₖ rₑ (m b)) ∙ ==-≡1₂.reflexive (!(m⁻¹-m b))

module Advantage
  where

  Rᵁ = Rₐᵁ ×ᵁ Rₖᵁ ×ᵁ Rₑᵁ

  run : Bit → Adversary → ℕ
  run b adv = count Rᵁ (EXP b adv)

  Advantage : Adversary → ℕ
  Advantage adv = dist (run 0b adv) (run 1b adv)
{-
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
