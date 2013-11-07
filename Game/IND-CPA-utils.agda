open import Type
open import Control.Strategy
open import Data.Product

module Game.IND-CPA-utils (Message CipherText : ★) where

-- This describes a "round" of decryption queries
DecRound : ★ → ★
DecRound = Strategy CipherText Message

record CPAAdversary (Next : ★) : ★ where
  constructor mk
  field
    get-m : Message × Message
    put-c : CipherText → Next
open CPAAdversary public

CPA†Adversary : (Next : ★) → ★
CPA†Adversary Next = CPAAdversary (CipherText → Next)
