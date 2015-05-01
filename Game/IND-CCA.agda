{-# OPTIONS --without-K #-}
open import Type
open import Data.Bit
open import Data.Product
open import Control.Strategy renaming (run to run-round)
open import Game.Challenge
open import Crypto.Schemes
import Game.IND-CPA-utils
  
module Game.IND-CCA
  (pke : Pubkey-encryption)
  (Rₐ : Type)
  where

open Pubkey-encryption pke

open Game.IND-CPA-utils Message CipherText

Adversary : Type
Adversary = Rₐ → PubKey → DecRound (CPAAdversary Bit)

R : Type
R = Rₐ × Rₖ × Rₑ

Experiment : Type
Experiment = Adversary → R → Bit

EXP : Bit → Experiment
EXP b A (rₐ , rₖ , rₑ) with key-gen rₖ
... | pk , sk = b' where
  A' = run-round (dec sk) (A rₐ pk)
  m  = get-chal A'
  c  = enc pk (m b) rₑ
  b' = put-resp A' c

game : Adversary → (Bit × R) → Bit
game A (b , r) = b == EXP b A r
