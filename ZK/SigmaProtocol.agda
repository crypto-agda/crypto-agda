open import Type                 using (Type)
open import Data.Bool.Base       using (Bool) renaming (T to ✓)
open import Relation.Binary.Core using (_≡_; _≢_)

-- See ZK.SigmaProtocol.KnownStatement for a simpler version which assumes the statement to
-- be known already by all parties.

module ZK.SigmaProtocol
          (Statement  : Type) -- Set of possible statements of the zk-proof
          (Commitment : Statement → Type) -- Prover commitments
          (Challenge  : Statement → Type) -- Verifier challenges, picked at random
          (Response   : Statement → Type) -- Prover responses/proofs to challenges
          (Randomness : Statement → Type) -- Prover's randomness
          (Witness    : Statement → Type) -- Prover's witness
          (_∋_        : (Y : Statement) → Witness Y → Type) -- Valid witness for a given statement
       where

import ZK.SigmaProtocol.Types as Common
open Common public using (_,_; mk)

-- The prover is made of two steps.
-- * First, send the commitment.
-- * Second, receive a challenge and send back the response.
--
-- Therefor one represents a prover as a pair (a record) made
-- of a commitment (get-A) and a function (get-f) from challenges
-- to responses.
--
-- Note that one might wish the function get-f to be partial.
--
-- This covers any kind of prover, either honest or dishonest
-- Notice as well that such should depend on some randomness.
-- So such a prover as type: SomeRandomness → Prover
Prover-Interaction : (Y : Statement) → Type
Prover-Interaction Y = Common.Prover-Interaction (Commitment Y) (Challenge Y) (Response Y)

module Prover-Interaction Y = Common.Prover-Interaction (Commitment Y) (Challenge Y) (Response Y)

Prover : Type
Prover = (Y : Statement)(r : Randomness Y)(w : Witness Y) → Prover-Interaction Y

Transcript : (Y : Statement) → Type
Transcript Y = Common.Transcript (Commitment Y) (Challenge Y) (Response Y)

module Transcript Y = Common.Transcript (Commitment Y) (Challenge Y) (Response Y)

-- The actual behavior of an interactive verifier is as follows:
-- * Given a statement
-- * Receive a commitment from the prover
-- * Send a randomly chosen challenge to the prover
-- * Receive a response to that challenge
-- Since the first two points are common to all Σ-protocols we describe
-- the verifier behavior as a computable test on the transcript.
Verifier : Type
Verifier = (Y : Statement)(t : Transcript Y) → Bool

-- To run the interaction, one only needs the prover and a randomly
-- chosen challenge. The returned transcript is then checked by the
-- verifier afterwards.
run : (Y : Statement) → Prover-Interaction Y → Challenge Y → Transcript Y
run Y prover c = mk get-A c (get-f c)
  where open Prover-Interaction Y prover

-- A Σ-protocol is made of the code for honest prover
-- and honest verifier.
record Σ-Protocol : Type where
  constructor _,_
  field
    prover   : Prover
    verifier : Verifier

  Verified : (Y : Statement)(t : Transcript Y) → Type
  Verified Y t = ✓ (verifier Y t)

  prover-commitment : (Y : Statement)(r : Randomness Y)(w : Witness Y) → Commitment Y
  prover-commitment Y r w = Prover-Interaction.get-A Y (prover Y r w)

  prover-response : (Y : Statement)(r : Randomness Y)(w : Witness Y)(c : Challenge Y) → Response Y
  prover-response Y r w = Prover-Interaction.get-f Y (prover Y r w)

-- Correctness (also called completeness in some papers): a Σ-protocol is said
-- to be correct if for any challenge, the (honest) verifier accepts what
-- the (honest) prover returns.
Correct : Σ-Protocol → Type
Correct (prover , verifier) = ∀ Y w r c → Y ∋ w → ✓ (verifier Y (run Y (prover Y r w) c))

-- A simulator takes a challenge and a response and returns a commitment.
--
-- As defined next, a correct simulator picks the commitment such that
-- the transcript is accepted by the verifier.
--
-- Notice that generally, to make a valid looking transcript one should
-- randomly pick the challenge and the response.
Simulator : Type
Simulator = (Y : Statement) (c : Challenge Y) (s : Response Y) → Commitment Y

-- A correct simulator always convinces the honest verifier.
Correct-simulator : Verifier → Simulator → Type
Correct-simulator verifier simulator
  = ∀ Y c s → let A = simulator Y c s in
              ✓(verifier Y (mk A c s))

{-
  A Σ-protocol, more specifically a verifier which is equipped with
  a correct simulator is said to be Special Honest Verifier Zero Knowledge.
  This property is one of the condition to apply the Strong Fiat Shamir
  transformation.

  The Special part of Special-Honest-Verifier-Zero-Knowledge is covered by the
  simulator being correct.

  The Honest part is not covered yet, the definition is informally adapted from
  the paper "How not to prove yourself":

  Furthermore, if the challenge c and response s where chosen uniformly at random from their respective
  domains then the triple (A, c, s) is distributed identically to that of an execution
  between the (honest) prover and the (honest) verifier (run prover c).

  where A = simulator c s
-}
record Special-Honest-Verifier-Zero-Knowledge (Σ-proto : Σ-Protocol) : Type where
  open Σ-Protocol Σ-proto
  field
    simulator          : Simulator
    .correct-simulator : Correct-simulator verifier simulator

Transcript² : (verifier : Verifier) (Y : Statement) → Type
Transcript² verifier Y = Common.Transcript² (Commitment Y) (Challenge Y) (Response Y) (verifier Y)

module Transcript² (Y : Statement) = Common.Transcript² (Commitment Y) (Challenge Y) (Response Y)

-- Remark: What if the underlying witnesses are different? Nothing is enforced here.
-- At least in the case of the Schnorr protocol it does not matter and yield a unique
-- witness.
Extractor : Verifier → Type
Extractor verifier = (Y : Statement) → Transcript² verifier Y → Witness Y

Extract-Valid-Witness : (verifier : Verifier) → Extractor verifier → Type
Extract-Valid-Witness verifier extractor = ∀ Y t² → Y ∋ extractor Y t²

-- A Σ-protocol, more specifically a verifier which is equipped with
-- a correct extractor is said to have the Special Soundness property.
-- This property is one of the condition to apply the Strong Fiat Shamir
-- transformation.
record Special-Soundness Σ-proto : Type where
  open Σ-Protocol Σ-proto
  field
  -- TODO Challenge should exp large wrt the security param
    extractor              : Extractor verifier
    .extract-valid-witness : Extract-Valid-Witness verifier extractor

record Special-Σ-Protocol : Type where
  field
    Σ-protocol : Σ-Protocol
    .correct : Correct Σ-protocol
    shvzk   : Special-Honest-Verifier-Zero-Knowledge Σ-protocol
    ssound  : Special-Soundness Σ-protocol
  open Σ-Protocol Σ-protocol public
  open Special-Honest-Verifier-Zero-Knowledge shvzk public
  open Special-Soundness ssound public
-- -}
-- -}
-- -}
-- -}
-- -}
