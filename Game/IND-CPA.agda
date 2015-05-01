{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Crypto.Schemes
import Game.IND-CPA.Core

module Game.IND-CPA
  (pke : Pubkey-encryption)
  (Rₐ : Type) -- Randomness for the adversary
  (Rₓ : Type) -- Randomness for "extensions"
  where

open Pubkey-encryption pke
open Game.IND-CPA.Core
  PubKey SecKey Message CipherText Rₑ Rₖ Rₐ Rₓ key-gen enc public
