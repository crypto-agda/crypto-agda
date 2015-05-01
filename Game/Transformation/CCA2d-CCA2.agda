{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.Two
open import Control.Strategy renaming (run to run-round; map to map-round)

open import Function

open import Relation.Binary.PropositionalEquality.NP

open import Crypto.Schemes
open import Game.Challenge
import Game.IND-CPA-utils
import Game.IND-CCA2-dagger.Adversary
import Game.IND-CCA2-dagger.Experiment
import Game.IND-CCA2
import Game.IND-CCA

module Game.Transformation.CCA2d-CCA2
  (pke : Pubkey-encryption)
  (Rₐ : Type)
  where

open Pubkey-encryption pke
module CCA2d  = Game.IND-CCA2-dagger.Adversary PubKey Message CipherText Rₐ
module CCA2dE = Game.IND-CCA2-dagger.Experiment pke Rₐ
module CCA2   = Game.IND-CCA2                   pke Rₐ
open Game.IND-CPA-utils Message CipherText

A-T' = CPAAdversary (DecRound Bit)
Ad-T' = CCA2d.Chal (DecRound Bit)

A-t' : A-T' → Ad-T'
A-t' = Map.A* id (λ f → f 0₂) id

A-transform : (adv : CCA2.Adversary) → CCA2d.Adversary
A-transform adv rₐ pk = map-round A-t' (adv rₐ pk)

{-
If we are able to do the transformation, then we get the same advantage
-}

dec-round = run-round ∘ dec

correct : ∀ {rₑ rₑ' rₖ rₐ } b adv
        → CCA2.EXP  b adv               (rₐ , rₖ , rₑ)
        ≡ CCA2dE.EXP b (A-transform adv) (rₐ , rₖ , rₑ , rₑ')
correct {rₑ} {rₑ'} {rₖ} {rₐ} b m with key-gen rₖ
... | pk , sk =
  rs (put-resp rm (enc pk (get-chal rm b) rₑ))
    ≡⟨ ap (λ x → rs (put-resp rm (enc pk x rₑ))) rmrmd ⟩
  rs (put-resp (A-t' (run-round (dec sk) (m rₐ pk))) kd)
    ≡⟨ ap (λ x → rs (put-resp x kd)) !rm ⟩
  rs (put-resp rmd kd) ∎
  where open ≡-Reasoning
        rs = run-round (dec sk)
        md = A-transform m rₐ pk
        rmd = rs md
        rm = rs (m rₐ pk)
        !rm = ! run-map (dec sk) A-t' (m rₐ pk)
        rmrmd = ap (λ x → get-chal x b) !rm
        kd = λ x → enc pk (get-chal rmd (x xor b)) ([0: rₑ 1: rₑ' ] x)
{-

Need to show that they are valid transformation aswell:

  This is not obvious that it will always work since the original adversary might
  ask for the ciphertext from the rₑ' supply.

  The argument why this is unlikely (in the paper) is that the construction is
  IND-CPA secure and therefor it is hard to predict a ciphertext.
  suppose that A could predict the ciphertext, then it could use this power to
  win the game. Since he can predict what enc(m(not b)) is he could just check what the
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
