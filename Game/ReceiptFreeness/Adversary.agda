open import Function
open import Type
open import Data.Fin as Fin
open import Data.Nat.NP using (ℕ)
open import Data.Two
open import Data.Product
import Data.List as L
open L using (List; _∷_ ; [])
open import Data.Vec

open import Game.Challenge
open import Control.Strategy

open import Relation.Binary.PropositionalEquality.NP as ≡

module Game.ReceiptFreeness.Adversary
  (PubKey SerialNumber² Rₐ Receipt Ballot Tally CO BB : ★) where

data Accept? : ★ where
  accept reject : Accept?

data Q : ★ where
  REB RBB RTally : Q
  RCO            : Receipt → Q
  Vote           : Receipt → Q

Resp : Q → ★
Resp REB = Ballot
Resp (RCO x) = CO
Resp (Vote x) = Accept?
Resp RBB = BB
Resp RTally = Tally

PhaseNumber : ★
PhaseNumber = 𝟚

Phase : ★ → ★
Phase = Strategy Q Resp

RFChallenge : ★ → ★
RFChallenge = ChalAdversary SerialNumber² (Receipt ²)

Adversary : ★
Adversary = Rₐ → PubKey → Phase -- Phase1
                           (RFChallenge -- give two serial numbers, get back two receipts
                             (Phase -- Phase2
                               𝟚)) -- Adversary guess of whether the vote is for alice
