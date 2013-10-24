{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary.PropositionalEquality

import Game.IND-CCA2-dagger
import Game.IND-CCA2
import Game.IND-CCA

module Game.Transformation.CCA2d-CCA2
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
open CCA2d using (DecRound)

f : (Message × Message) × (CipherText → DecRound Bit)
  → (Message × Message) × (CipherText → CipherText → DecRound Bit)
f (m , g) = m , λ c _ → g c

A-transform : (adv : CCA2.Adv) → CCA2d.Adv
A-transform adv rₐ pk = mapStrategy f (adv rₐ pk)
  
{-

If we are able to do the transformation, then we get the same advantage

-}

decRound = runStrategy ∘ Dec

correct : ∀ {rₑ rₑ' rₖ rₐ } b adv
        → CCA2.⅁  b adv               (rₐ , rₖ , rₑ)
        ≡ CCA2d.⅁ b (A-transform adv) (rₐ , rₖ , rₑ , rₑ')
correct {rₑ} {rₑ'} {rₖ} {rₐ} 0b m with KeyGen rₖ
... | pk , sk = cong (λ x → decRound sk (proj₂ x (Enc pk (proj₁ (proj₁ x)) rₑ)
                                             (Enc pk (proj₂ (proj₁ x)) rₑ')))
                     (sym (run-map (Dec sk) f (m rₐ pk)))
correct {rₑ}{rₑ'}{rₖ} {rₐ} 1b m with KeyGen rₖ
... | pk , sk = cong (λ x → decRound sk (proj₂ x (Enc pk (proj₂ (proj₁ x)) rₑ)
                                             (Enc pk (proj₁ (proj₁ x)) rₑ')))
                     (sym (run-map (Dec sk) f (m rₐ pk)))
{-

Need to show that they are valid transformation aswell:

  This is not obvious that it will always work since the original adversary might
  ask for the ciphertext from the rₑ' supply.

  The argument why this is unlikely (in the paper) is that the construction is
  IND-CPA secure and therefor it is hard to predict a ciphertext.
  suppose that A could predict the ciphertext, then it could use this power to
  win the game. Since he can predict what Enc(m(not b)) is he could just check what the
  ciphertext was and that he received and thereby know if he received b or not b.

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
