
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

module Game.CCA2-CCA2d
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

module CCA2d = Game.IND-CCA2-dagger PubKey SecKey Message CipherText
    Rₑ Rₖ Rₐ KeyGen Enc Dec 
module CCA2 X = Game.IND-CCA2  PubKey SecKey Message CipherText
    Rₑ Rₖ (X × Rₐ) KeyGen Enc Dec
open import Game.CCA-Common Message CipherText
open Eval Dec

X = Bit × Rₑ

f : PubKey → Bit → Rₑ
  → (Message × Message) × (CipherText → CipherText → Strategy Bit)
  → (Message × Message) × (CipherText → Strategy Bit)
f pk b rₑ (m , g) = (m , λ c → g c (Enc pk (proj m b) rₑ))

A-transform : (adv : CCA2d.Adv) → CCA2.Adv X
A-transform adv ((b , rₑ) , rₐ) pk = Follow (f pk b rₑ) (adv rₐ pk)

correct : ∀ {rₑ rₑ' rₐₑ rₖ rₐ} b adv
        → CCA2d.⅁  b adv               (rₐ , rₖ , rₑ , rₑ')
        ≡ CCA2.⅁ X b (A-transform adv) (((b , rₐₑ) , rₐ) , rₖ , rₑ)
correct {rₑ}{rₐₑ = ra}{rₖ = r}{rₐ} 1b adv with KeyGen r
... | pk , sk  =  trans {!refl!} (cong (λ x → eval sk (proj₂ x (Enc pk (proj₂ (proj₁ x)) rₑ)))
                      (sym (eval-Follow sk (f pk 1b ra) (adv rₐ pk))) )
correct {rₑ}{rₐₑ = ra}{rₖ = r}{rₐ} 0b adv with KeyGen r
... | pk , sk = trans {!refl!} (cong (λ x → eval sk (proj₂ x (Enc pk (proj₁ (proj₁ x)) rₑ))) (sym (eval-Follow sk (f pk 0b ra) (adv rₐ pk))))

{-

Need to show that they are valid aswell

-}

{-
valid : ∀ adv → CCA2d.Valid-Adv adv → CCA2.Valid-Adv Bit (A-transform adv)
valid adv valid = {!!}
-}


-- -}
-- -}
-- -}
-- -}
-- -}
