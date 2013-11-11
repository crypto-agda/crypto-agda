{-# OPTIONS --copatterns #-}
open import Type
open import Control.Strategy
open import Data.Product

module Game.IND-CPA-utils (Message CipherText : ★) where

-- This describes a "round" of decryption queries
DecRound : ★ → ★
DecRound = Strategy CipherText (λ _ → Message)

record CPAAdversary (Next : ★) : ★ where
  field
    get-m : Message × Message
    put-c : CipherText → Next
open CPAAdversary public

CPA†Adversary : (Next : ★) → ★
CPA†Adversary Next = CPAAdversary (CipherText → Next)

module TransformAdversaryResponse {X Y : ★} (f : X → Y) (A : CPAAdversary X) where
  A* : CPAAdversary Y
  get-m A*   = get-m A
  put-c A* c = f (put-c A c)
