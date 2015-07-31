{-# OPTIONS --without-K #-}
open import Type                 using (Type)
open import Data.Bool.Base       using (Bool) renaming (T to ✓)
open import Relation.Binary.Core using (_≡_; _≢_)
import ZK.SigmaProtocol.Types

-- This module assumes the exact statement of the Zero-Knowledge proof to be
-- known by all parties.
module ZK.SigmaProtocol.KnownStatement
          (Commitment : Type) -- Prover commitments
  -- TODO Challenge should exp large wrt the security param
          (Challenge  : Type) -- Verifier challenges, picked at random
          (Response   : Type) -- Prover responses/proofs to challenges
          (Randomness : Type) -- Prover's randomness
          (Witness    : Type) -- Prover's witness
          (ValidWitness : Witness → Type) -- Valid witness for the statement
       where

-- See the module ZK.Types for details about the types:
--   * Prover-Interaction
--   * Verifier
--   * Transcript
--   * Transcript²
open ZK.SigmaProtocol.Types Commitment Challenge Response public

Prover : Type
Prover = (r : Randomness)(w : Witness) → Prover-Interaction

-- To run the interaction, one only needs the prover and a randomly
-- chosen challenge. The returned transcript is then checked by the
-- verifier afterwards.
run : Prover-Interaction → Challenge → Transcript
run (A , f) c = mk A c (f c)

_⇆_ : Verifier → Prover → (r : Randomness)(w : Witness)(c : Challenge) → Bool
(verifier ⇆ prover) r w c = verifier (run (prover r w) c)

-- A Σ-protocol is made of the code for honest prover
-- and honest verifier.
record Σ-Protocol : Type where
  constructor _,_
  field
    prover   : Prover
    verifier : Verifier

  Verified : (t : Transcript) → Type
  Verified t = ✓ (verifier t)

  prover-commitment : (r : Randomness)(w : Witness) → Commitment
  prover-commitment r w = Prover-Interaction.get-A (prover r w)

  prover-response : (r : Randomness)(w : Witness)(c : Challenge) → Response
  prover-response r w = Prover-Interaction.get-f (prover r w)

-- Correctness (also called completeness in some papers): a Σ-protocol is said
-- to be correct if for any challenge, the (honest) verifier accepts what
-- the honest prover returns.
Correct : Σ-Protocol → Type
Correct (prover , verifier) = ∀ w r c (w? : ValidWitness w) →
                              ✓ ((verifier ⇆ prover) r w c)

-- A simulator takes a challenge and a response and returns a commitment (to be used to prove the Special Honest Verifier Zero-Knowledge property).
--
-- As defined next, a correct simulator picks the commitment such that
-- the transcript is accepted by the verifier.
--
-- Notice that generally, to make a valid looking transcript one should
-- randomly pick the challenge and the response.
Simulator : Type
Simulator = (c : Challenge) (s : Response) → Commitment

-- A correct simulator always convinces the honest verifier.
Correct-simulator : Verifier → Simulator → Type
Correct-simulator verifier simulator
  = ∀ c s → let A = simulator c s in
            ✓ (verifier (mk A c s))

{-
  A Σ-protocol is said to be Special Honest Verifier Zero-Knowledge if there is a correct simulator.
  This property is one of the necessary conditions to apply the Strong Fiat Shamir
  transformation.

  The Honest part is not covered yet, the definition is informally adapted from
  the paper "How not to prove yourself":

  Furthermore, if the challenge c and response s where chosen uniformly at random from their respective
  domains then the triple (A, c, s) is distributed identically to that of an execution
  between the honest prover and the (honest) verifier (run prover c).

  where A = simulator c s
-}
record Special-Honest-Verifier-Zero-Knowledge (Σ-proto : Σ-Protocol) : Type where
  open Σ-Protocol Σ-proto
  field
    simulator          : Simulator
    .correct-simulator : Correct-simulator verifier simulator

-- Remark: What if the underlying witnesses are different? Nothing is enforced here.
-- At least in the case of the Schnorr protocol it does not matter and yield a unique
-- witness.
Extractor : Verifier → Type
Extractor verifier = (t² : Transcript² verifier) → Witness

Extract-Valid-Witness : (verifier : Verifier) → Extractor verifier → Type
Extract-Valid-Witness verifier extractor = ∀ t² → ValidWitness (extractor t²)

-- A Σ-protocol, more specifically a verifier which is equipped with
-- a correct knowledge extractor is said to have the Special Soundness property.
-- This property is one of the conditions needed to apply the Strong Fiat Shamir
-- transformation.
-- Also called 2-extractable
record Special-Soundness Σ-proto : Type where
  open Σ-Protocol Σ-proto
  field
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
