{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Function
open import Data.Bit
open import Data.Maybe
open import Data.Two.Equality
open import Data.Product.NP

open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy renaming (run to run-round)

open import Game.Challenge
open import Crypto.Schemes
import Game.IND-CPA-utils
import Game.IND-CCA

{-
Notice that this formalisation of IND-CCA2 does not enforce
the second round of oracle calls to not include the challenge.

This remains to be integrated in one of the following ways:
* Part of the adversary type
* Part of the dynamic run of the game
  * By checking each query
  * Or by checking the transcript at the end [*]
* As a separate predecate on adversaries

As a reminder we provide a cheating adversary with the prove
that he wins the game.
-}
module Game.IND-CCA2
  (pke : Pubkey-encryption)
  (Rₐ : Type)
  where

open Pubkey-encryption pke
module CCA = Game.IND-CCA pke
open Game.IND-CPA-utils Message CipherText public

Adversary : ★
Adversary = Rₐ → PubKey →
                   DecRound            -- first round of decryption queries
                     (CPAAdversary     -- choosen plaintext attack
                       (DecRound Bit)) -- second round of decryption queries

R : ★
R = Rₐ × Rₖ × Rₑ

EXP : Bit → Adversary → R → Bit
EXP b A (rₐ , rₖ , rₑ) = b'
  module EXP where
    k         = key-gen rₖ
    pk        = fst k
    sk        = snd k
    round1    = run-round (dec sk) (A rₐ pk)
    m         = get-chal round1
    c         = enc pk (m b) rₑ
    round2    = put-resp round1 c
    b'        = run-round (dec sk) round2

game : Adversary → (Bit × R) → Bit
game A (b , r) = b == EXP b A r

module Cheating
   -- The two messages, m₀ and m₁ are seen as a function from 𝟚 to Message.
   -- m⁻¹ takes a message and tell whever this is m₀ or m₁.
   (m : Message ²)
   (m⁻¹ : Message → Bit)
   (m⁻¹-m : ∀ x → m⁻¹ (m x) ≡ x)
   where

  cheatingA : Adversary
  cheatingA rₐ pk = done CPApart
    module cheatingA where
      dummy = m 0b
      CPApart : CPAAdversary _
      get-chal CPApart   = m
      put-resp CPApart c = ask c (done ∘ m⁻¹ ∘ maybe id dummy)

  cheatingA-always-wins : ∀ r → game cheatingA r ≡ 1b
  cheatingA-always-wins (b , rₐ , rₖ , rₑ) =
    ap (_==_ b ∘ m⁻¹ ∘ maybe id (m 0b)) (functionally-correct rₖ rₑ (m b)) ∙ ==-≡1₂.reflexive (!(m⁻¹-m b))

-- -}
-- -}
-- -}
-- -}
