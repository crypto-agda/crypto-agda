open import Type
open import Data.Two

module ZK.Sigma-Protocol (Commitment Challenge Response : ★) where

  record Prover : ★ where
    constructor _,_
    field
      get-A : Commitment
      get-f : Challenge → Response

  record Transcript : ★ where
    constructor mk
    field
      get-A : Commitment
      get-c : Challenge
      get-f : Response

  Verifier : ★
  Verifier = Transcript → 𝟚

  run : Prover → Challenge → Transcript
  run (A , f) c = mk A c (f c)

  Correctness : Prover → Verifier → ★
  Correctness prover verifier
    = ∀ c → ✓ (verifier (run prover c))
