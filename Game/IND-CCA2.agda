
{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Unit


open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2
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
open import Game.CCA-Common Message CipherText Rₓ 
                         
AdvStep₀ : ★
AdvStep₀ = Rₐ → PubKey → MessageStrategy
    
    
AdvStep₁ : ★
AdvStep₁ = Rₐ' → Rₓ → PubKey → (c : CipherText) → CipherStrategy

Adv : ★
Adv = AdvStep₀ × AdvStep₁

Valid-Adv : Adv → Set
Valid-Adv (m , d) = ∀ {rₐ rₓ pk c} → Valid (λ x → x ≢ c) (d rₐ rₓ pk c)

R : ★
R = Rₐ × Rₐ' × Rₖ × Rₑ

Game : ★
Game = Adv → R → Bit


⅁ : Bit → Game
⅁ b (m , d) (rₐ , rₐ' , rₖ , rₑ) with KeyGen rₖ
... | pk , sk = b′ where
  open Eval Dec sk
  
  ev = evalM (m rₐ pk)
  mb = proj (proj₁ ev) b
  rₓ = proj₂ ev

  c  = Enc pk mb rₑ
  b′ = evalC (d rₐ' rₓ pk c)

-- -}
-- -}
-- -}
-- -}
