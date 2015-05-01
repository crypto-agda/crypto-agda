{-# OPTIONS --without-K #-}
open import Type
open import Data.Two
open import Data.Product

open import Game.Challenge
open import Control.Strategy

module Game.ReceiptFreeness.Adversary
  (PubKey SerialNumber² Rₐ Receipt Ballot Tally CO BB : ★) where

data Accept? : ★ where
  accept reject : Accept?

PhaseNumber : ★
PhaseNumber = 𝟚

Receipt² = Receipt ²

data Query : ★ where
  REB RBB RTally : Query
  RCO Vote       : Receipt → Query

Resp : Query → ★
Resp REB      = Ballot  -- Request Empty Ballot
Resp (RCO x)  = CO      -- Request Candidate Order
Resp (Vote x) = Accept? -- Vote
Resp RBB      = BB      -- Request Ballot Box
Resp RTally   = Tally   -- Request Tally

{-
data OraclePhase (A : ★) : ★ where
  ask  : -- Send a query
         (q : Query)
         -- Receive the corresponding response
         (cont : Resp q → OraclePhase A)
       → OraclePhase A
  done : A → OraclePhase A

Adversary : ★
Adversary = Rₐ →            -- Receive randomness
            PubKey →        -- Receive public key
            OraclePhase     -- Phase 1 of oracle queries
           (SerialNumber² × -- Send two serial numbers
            Receipt² →      -- Receive back two receipts
            OraclePhase     -- Phase 2 of oracle queries
            𝟚)              -- Guess if the vote is for alice
-}

Q = Query
OraclePhase = Strategy Q Resp
RFChallenge = ChalAdversary SerialNumber² Receipt²
Phase = OraclePhase

Adversary : ★
Adversary = Rₐ →            -- Receive randomness
            PubKey →        -- Receive public key
            OraclePhase     -- Phase 1 of oracle queries
           (RFChallenge     -- Send two serial numbers
                            -- Receive back two receipts
           (OraclePhase     -- Phase 2 of oracle queries
            𝟚))             -- Guess if the vote is for alice
-- -}
