{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Zero
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary.PropositionalEquality

open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base


import Game.IND-CPA-utils
import Game.IND-CCA2-dagger
import Game.IND-CCA2
import Game.IND-CCA

module Game.Transformation.CCA2d-CCA2
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

module CCA2d = Game.IND-CCA2-dagger PubKey SecKey Message CipherText Rₑᵁ Rₖᵁ Rₐᵁ KeyGen Enc Dec
module CCA2  = Game.IND-CCA2        PubKey SecKey Message CipherText Rₑᵁ Rₖᵁ Rₐᵁ KeyGen Enc Dec
open Game.IND-CPA-utils Message CipherText

{-
open TransformAdversaryResponse {DecRound Bit} {CipherText → DecRound Bit} (λ x _ → x)
-}

A-transform : (adv : CCA2.Adversary) → CCA2d.Adversary
A-transform adv rₐ pk = mapStrategy A* (adv rₐ pk)

{-
If we are able to do the transformation, then we get the same advantage
-}

{-
decRound = runStrategy ∘ Dec

correct : ∀ {rₑ rₑ' rₖ rₐ } b adv
        → CCA2.EXP b adv               (rₐ , rₖ , rₑ)
        ≡ CCA2d.EXP b (A-transform adv) (rₐ , rₖ , rₑ , rₑ')
correct {rₑ} {rₑ'} {rₖ} {rₐ} 0b m with KeyGen rₖ
... | pk , sk = cong (λ x → decRound sk (put-c x (Enc pk (proj₁ (get-m x)) rₑ)
                                                 (Enc pk (proj₂ (get-m x)) rₑ')))
                     (sym (run-map (Dec sk) A* (m rₐ pk)))
correct {rₑ}{rₑ'}{rₖ} {rₐ} 1b m with KeyGen rₖ
... | pk , sk = cong (λ x → decRound sk (put-c x (Enc pk (proj₂ (get-m x)) rₑ)
                                                 (Enc pk (proj₁ (get-m x)) rₑ')))
                     (sym (run-map (Dec sk) A* (m rₐ pk)))
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
