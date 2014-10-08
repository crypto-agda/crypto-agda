module ZK.Schnorr where

open import Type
open import Data.Two
open import Relation.Binary.PropositionalEquality.NP
import ZK.Sigma-Protocol

module Shnorr-protocol
    (G ℤq : ★)
    (g    : G)
    (_^_  : G  → ℤq → G)
    (_·_  : G  → G  → G)
    (_/_  : G  → G  → G)
    (_+_  : ℤq → ℤq → ℤq)
    (_*_  : ℤq → ℤq → ℤq)
    (_==_ : (x y : G) → 𝟚)
    where

  Commitment = G
  Challenge  = ℤq
  Response   = ℤq

  open ZK.Sigma-Protocol Commitment Challenge Response

  module _ (x w : ℤq) where
    prover-commitment : Commitment
    prover-commitment = g ^ w

    prover-response : Challenge → Response
    prover-response c = w + (x * c)

    prover : Prover
    prover = prover-commitment , prover-response

  module _ (y : G) where
    verifier : Verifier
    verifier (mk A c s) = (g ^ s) == (A · (y ^ c))

    -- This simulator shows why it is so important for the
    -- challenge to be picked once the commitment is known.
    
    -- To fake a transcript, the challenge and response can
    -- be arbitrarily chosen. However to be indistinguishable
    -- from a valid proof it they need to be picked at random.
    module _ (c : Challenge) (s : Response) where
        -- Compute A, such that the verifier accepts!
        private
            A = (g ^ s) / (y ^ c)

        simulate-commitment : Commitment
        simulate-commitment = A

        simulate : Transcript
        simulate = mk simulate-commitment c s

        module Correct-simulation
           (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
           (/-·  : ∀ {P Q} → P ≡ (P / Q) · Q)
          where
          correct-simulation : ✓(verifier simulate)
          correct-simulation = ✓-== /-·

  module Correctness-proof
           (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
           (^-+  : ∀ {b x y} → b ^(x + y) ≡ (b ^ x) · (b ^ y))
           (^-*  : ∀ {b x y} → b ^(x * y) ≡ (b ^ x) ^ y)
           (x r  : ℤq) where
    open ≡-Reasoning
    gʳ = g ^ r
    correctness : Correctness (prover x r) (verifier (g ^ x))
    correctness c = ✓-== (g ^(r + (x * c))
                        ≡⟨ ^-+ ⟩
                         gʳ · (g ^(x * c))
                        ≡⟨ ap (λ z → gʳ · z) ^-* ⟩
                         gʳ · ((g ^ x) ^ c)
                        ∎)

-- -}
-- -}
-- -}
-- -}
