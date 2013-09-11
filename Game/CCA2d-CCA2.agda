{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Unit

open import Function

open import Relation.Binary.PropositionalEquality

import Game.IND-CCA2-dagger
import Game.IND-CCA2
import Game.IND-CCA

module Game.CCA2d-CCA2
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

module CCA2d = Game.IND-CCA2-dagger PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec 
module CCA2  = Game.IND-CCA2        PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec

open import Game.CCA-Common Message CipherText

open Eval Dec

f : (Message × Message) × (CipherText → Strategy Bit)
  → (Message × Message) × (CipherText → CipherText → Strategy Bit)
f (m , g) = m , λ c _ → g c

A-transform : (adv : CCA2.Adv) → CCA2d.Adv
A-transform adv rₐ pk = Follow f (adv rₐ pk)
  
correct : ∀ {rₑ rₖ rₐ } b adv
        → CCA2.⅁  b adv               (rₐ , rₖ , rₑ)
        ≡ CCA2d.⅁ b (A-transform adv) (rₐ , rₖ , rₑ , rₑ)
correct {rₑ} {rₖ} {rₐ} 0b m with KeyGen rₖ
... | pk , sk = cong (λ x → eval sk (proj₂ x (Enc pk (proj₁ (proj₁ x)) rₑ)
                                             (Enc pk (proj₂ (proj₁ x)) rₑ)))
                     (sym (eval-Follow sk f (m rₐ pk)))
correct {rₑ} {rₖ} {rₐ} 1b m with KeyGen rₖ
... | pk , sk = cong (λ x → eval sk (proj₂ x (Enc pk (proj₂ (proj₁ x)) rₑ)
                                             (Enc pk (proj₁ (proj₁ x)) rₑ)))
                     (sym (eval-Follow sk f (m rₐ pk)))
{-

Need to show that they are valid aswell

-}

{-
valid : ∀ adv → CCA2.Valid-Adv adv → CCA2d.Valid-Adv (A-transform adv)
valid adv valid = {!!} -- can't prove this strictly, but it will deviate with
                       -- non-neg probability

-- -}
-- -}
-- -}
-- -}
-- -}
