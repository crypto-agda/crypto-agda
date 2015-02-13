open import Type                 using (Type)
open import Data.Bool.Base       using (Bool; true)
open import Relation.Binary.Core using (_≡_; _≢_)

-- This module assumes the exact statement of the Zero-Knowledge proof to be
-- known by all parties.
module ZK.SigmaProtocol.KnownStatement
          (Commitment : Type) -- Prover commitments
          (Challenge  : Type) -- Verifier challenges, picked at random
          (Response   : Type) -- Prover responses/proofs to challenges
          (Randomness : Type) -- Prover's randomness
          (Witness    : Type) -- Prover's witness
          (ValidWitness : Witness → Type) -- Valid witness for the statement
       where

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
record Prover-Interaction : Type where
  constructor _,_
  field
    get-A : Commitment
    get-f : Challenge → Response

Prover : Type
Prover = (r : Randomness)(w : Witness) → Prover-Interaction

-- A transcript of the interaction between the prover and the
-- verifier.
--
-- Note that in the case of an interactive zero-knowledge
-- proof the transcript alone does not prove anything. It can usually
-- be simulated if one knows the challenge before the commitment.
--
-- The only way to be convinced by an interactive prover is to be/trust the verifier,
-- namely to receive the commitment first and send a randomly picked challenge
-- thereafter. So the proof is not transferable.
--
-- The other way is by making the zero-knowledge proof non-interactive, which forces the
-- challenge to be a cryptographic hash of the commitment and the statement.
-- See the StrongFiatShamir module and the corresponding paper for more details.
record Transcript : Type where
  constructor mk
  field
    get-A : Commitment
    get-c : Challenge
    get-f : Response

-- The actual behavior of an interactive verifier is as follows:
-- * Given a statement
-- * Receive a commitment from the prover
-- * Send a randomly chosen challenge to the prover
-- * Receive a response to that challenge
-- Since the first two points are common to all Σ-protocols we describe
-- the verifier behavior as a computable test on the transcript.
Verifier : Type
Verifier = (t : Transcript) → Bool

-- To run the interaction, one only needs the prover and a randomly
-- chosen challenge. The returned transcript is then checked by the
-- verifier afterwards.
run : Prover-Interaction → Challenge → Transcript
run (A , f) c = mk A c (f c)

-- A Σ-protocol is made of the code for honest prover
-- and honest verifier.
record Σ-Protocol : Type where
  constructor _,_
  field
    prover   : Prover
    verifier : Verifier

  Verified : (t : Transcript) → Type
  Verified t = verifier t ≡ true

-- Correctness (also called completeness in some papers): a Σ-protocol is said
-- to be correct if for any challenge, the (honest) verifier accepts what
-- the (honest) prover returns.
Correct : Σ-Protocol → Type
Correct (prover , verifier) = ∀ r {w} c → ValidWitness w → verifier (run (prover r w) c) ≡ true

-- A simulator takes a challenge and a response and returns a commitment.
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
            verifier (mk A c s) ≡ true

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
    simulator         : Simulator
    correct-simulator : Correct-simulator verifier simulator

-- A pair of "Transcript"s such that the commitment is shared
-- and the challenges are different.
record Transcript² (verifier : Verifier) : Type where
  constructor mk
  field
    -- The commitment is shared
    get-A         : Commitment

    -- The challenges...
    get-c₀ get-c₁ : Challenge

    -- ...are different
    c₀≢c₁         : get-c₀ ≢ get-c₁

    -- The responses/proofs are arbitrary
    get-f₀ get-f₁ : Response

  -- The two transcripts
  t₀ : Transcript
  t₀ = mk get-A get-c₀ get-f₀
  t₁ : Transcript
  t₁ = mk get-A get-c₁ get-f₁

  field
    -- The transcripts verify
    verify₀ : verifier t₀ ≡ true
    verify₁ : verifier t₁ ≡ true

-- Remark: What if the underlying witnesses are different? Nothing is enforced here.
-- At least in the case of the Schnorr protocol it does not matter and yield a unique
-- witness.
Extractor : Verifier → Type
Extractor verifier = Transcript² verifier → Witness

Extract-Valid-Witness : (verifier : Verifier) → Extractor verifier → Type
Extract-Valid-Witness verifier extractor = ∀ t² → ValidWitness (extractor t²)

-- A Σ-protocol, more specifically a verifier which is equipped with
-- a correct extractor is said to have the Special Soundness property.
-- This property is one of the condition to apply the Strong Fiat Shamir
-- transformation.
record Special-Soundness Σ-proto : Type where
  open Σ-Protocol Σ-proto
  field
  -- TODO Challenge should exp large wrt the security param
    extractor             : Extractor verifier
    extract-valid-witness : Extract-Valid-Witness verifier extractor

record Special-Σ-Protocol : Type where
  field
    Σ-protocol : Σ-Protocol
    correct : Correct Σ-protocol
    shvzk   : Special-Honest-Verifier-Zero-Knowledge Σ-protocol
    ssound  : Special-Soundness Σ-protocol
  open Σ-Protocol Σ-protocol public
  open Special-Honest-Verifier-Zero-Knowledge shvzk public
  open Special-Soundness ssound public
