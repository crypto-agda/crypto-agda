{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Zero
open import Data.Two
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary.PropositionalEquality.NP

open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base

open import Game.Challenge
import Game.IND-CPA-utils
import Game.IND-CCA2-dagger.Adversary
import Game.IND-CCA2
import Game.IND-CCA

module Game.Transformation.CCA2d-CCA2
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  --(Rₑᵁ Rₖᵁ Rₐᵁ : U)
  --(let Rₑ = El Rₑᵁ ; Rₖ = El Rₖᵁ ; Rₐ = El Rₐᵁ)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)

  where

module CCA2d = Game.IND-CCA2-dagger.Adversary PubKey        Message CipherText      Rₐ
module CCA2  = Game.IND-CCA2                  PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec
open Game.IND-CPA-utils Message CipherText

A-T' = CPAAdversary (DecRound Bit)
Ad-T' = CCA2d.Chal (DecRound Bit)

A-t' : A-T' -> Ad-T'
A-t' = Map.A* id (λ f → f 0₂) id

A-transform : (adv : CCA2.Adversary) → CCA2d.Adversary
A-transform adv rₐ pk = mapStrategy A-t' (adv rₐ pk)

{-
If we are able to do the transformation, then we get the same advantage
-}

decRound = runStrategy ∘ Dec

correct : ∀ {rₑ rₑ' rₖ rₐ } b adv
        → CCA2.EXP  b adv               (rₐ , rₖ , rₑ)
        ≡ CCA2d.EXP b (A-transform adv) (rₐ , rₖ , rₑ , rₑ')
correct {rₑ} {rₑ'} {rₖ} {rₐ} b m with KeyGen rₖ
... | pk , sk =
  rs (put-resp rm (Enc pk (get-chal rm b) rₑ))
    ≡⟨ ap (λ x → rs (put-resp rm (Enc pk x rₑ))) rmrmd ⟩
  rs (put-resp (A-t' (runStrategy (Dec sk) (m rₐ pk))) kd)
    ≡⟨ ap (\ x -> rs (put-resp x kd)) !rm ⟩
  rs (put-resp rmd kd) ∎
  where open ≡-Reasoning
        rs = runStrategy (Dec sk)
        md = A-transform m rₐ pk
        rmd = rs md
        rm = rs (m rₐ pk)
        !rm = ! run-map (Dec sk) A-t' (m rₐ pk)
        rmrmd = ap (λ x → get-chal x b) !rm
        kd = λ x → Enc pk (get-chal rmd (x xor b)) ([0: rₑ 1: rₑ' ] x)
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
