
{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.One
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary.PropositionalEquality

import Game.IND-CPA-dagger
import Game.IND-CPA

module Game.Transformation.CPAd-CPA
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

module CPAd = Game.IND-CPA-dagger PubKey SecKey Message CipherText Rₑ Rₖ Rₐ 𝟙 KeyGen Enc
module CPA  = Game.IND-CPA        PubKey SecKey Message CipherText Rₑ Rₖ Rₐ 𝟙 KeyGen Enc
--open CPAd using (DecRound)

{-
f : (Message × Message) × (CipherText → DecRound Bit)
  → (Message × Message) × (CipherText → CipherText → DecRound Bit)
f (m , g) = m , λ c _ → g c
-}


A-transform : (adv : CPA.Adv) → CPAd.Adv
A-transform (adv₁ , adv₂) = adv₁ , adv₂'
  where
    adv₂' : ∀ _ _ _ _ → _
    adv₂' rₐ pk c₀ c₁ = adv₂ rₐ pk c₀


{-

If we are able to do the transformation, then we get the same advantage

-}


correct : ∀ {rₑ rₑ' rₖ rₐ } b adv
        → CPA.⅁  b adv               (rₐ , rₖ , rₑ , _)
        ≡ CPAd.⅁ b (A-transform adv) (rₐ , rₖ , rₑ , rₑ' , _)
correct b adv = refl

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
