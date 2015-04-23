
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product

open import Data.Nat.NP
--open import Rat

open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open Operators
open import Control.Strategy renaming (run to runStrategy)
open import Game.Challenge
import Game.IND-CPA-utils

open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2-dagger.Adversary
  (PubKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for adversary state
  (Rₐ : ★)

  where

open Game.IND-CPA-utils Message CipherText

Chal = ChalAdversary      -- choosen plaintext attack (†)
           (Message ²)    --   the adversary picks two messages
           (CipherText ²) --   receives the encryption of both of them in a random order

Adversary : ★
Adversary = Rₐ → PubKey →
                   DecRound            -- first round of decryption queries
                     (Chal
                        (DecRound      -- second round of decryption queries
                           𝟚))         -- the adversary has to guess which message is encrypted as the first ciphertext
