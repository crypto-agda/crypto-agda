{-# OPTIONS --copatterns #-}
open import Type
open import Control.Strategy
open import Data.Two
open import Data.Maybe
open import Data.Product
open import Game.Challenge

module Game.IND-CPA-utils (Message CipherText : ★) where

--DecProto : Proto
--DecProto = P[ CipherText , λ _ → Message ]

-- This describes a "round" of decryption queries
DecRound : ★ → ★
DecRound = Strategy CipherText (λ _ → Maybe Message)

CPAAdversary : (Next : ★) → ★
CPAAdversary = ChalAdversary (Message ²) CipherText

CPAChallenger : (Next : ★) → ★
CPAChallenger Next = Message ² → CipherText × Next

CPA†Adversary : (Next : ★) → ★
CPA†Adversary = ChalAdversary (Message ²) (CipherText ²)

CPA†Challenger : (Next : ★) → ★
CPA†Challenger Next = Message ² → CipherText ² × Next
