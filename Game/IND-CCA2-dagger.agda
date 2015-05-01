{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Data.Zero
open import Data.Two
open import Data.Product
open import Data.Maybe
open import Data.Nat.NP
open import Relation.Binary.PropositionalEquality

open import Explore.Universe.Type {𝟘}
open import Explore.Universe.Base

open import Crypto.Schemes
open import Game.Challenge
import Game.IND-CPA-utils
import Game.IND-CCA2-dagger.Adversary
import Game.IND-CCA2-dagger.Valid
import Game.IND-CCA2-dagger.Experiment

module Game.IND-CCA2-dagger
  (PubKey    : Type)
  (SecKey    : Type)
  (Message   : Type)
  (CipherText : Type)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑᵁ Rₖᵁ Rₐᵁ : U)
  (let Rₑ = El Rₑᵁ ; Rₖ = El Rₖᵁ ; Rₐ = El Rₐᵁ)
  (key-gen : Rₖ → PubKey × SecKey)
  (enc    : PubKey → Message → Rₑ → CipherText)
  (dec    : SecKey → CipherText → Maybe Message)

  (functionally-correct :
    ∀ rₖ rₑ m → let (pk , sk) = key-gen rₖ in
               dec sk (enc pk m rₑ) ≡ just m)
  where

pke : Pubkey-encryption
pke = record
        { pkt = record
          { PubKey = PubKey
          ; SecKey = SecKey
          ; Message = Message
          ; CipherText = CipherText
          ; Rₖ = Rₖ
          ; Rₑ = Rₑ }
        ; pko = record
          { key-gen = key-gen
          ; enc = enc
          ; dec = dec
          }
        ; functionally-correct = functionally-correct
        }

open Game.IND-CCA2-dagger.Valid PubKey Message CipherText Rₐ public
open Game.IND-CCA2-dagger.Experiment pke Rₐ public

Rᵁ = Rₐᵁ ×ᵁ Rₖᵁ ×ᵁ Rₑᵁ ×ᵁ Rₑᵁ

run : 𝟚 → Adversary → ℕ
run b adv = count Rᵁ (EXP b adv)

{-
  Advantage : Adv → ℚ
  Advantage adv = dist (run 0b adv) (run 1b adv) / Card Rᵁ
-}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
