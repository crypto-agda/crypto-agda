{-# OPTIONS --without-K #-}
open import Type using (Type; Type₁)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.Core using (_≢_)

module ZK.SigmaProtocol.Types (Commitment Challenge Response : Type) where
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
      verify₀ : ✓ (verifier t₀)
      verify₁ : ✓ (verifier t₁)
