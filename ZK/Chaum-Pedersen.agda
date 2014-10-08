open import Type
open import Data.Two
open import Relation.Binary.PropositionalEquality.NP
import ZK.Sigma-Protocol

module ZK.Chaum-Pedersen
    (G ℤq : ★)
    (g    : G)
    (_^_  : G  → ℤq → G)
    (_·_  : G  → G  → G)
    (_/_  : G  → G  → G)
    (_+_  : ℤq → ℤq → ℤq)
    (_*_  : ℤq → ℤq → ℤq)
    (_==_ : (x y : G) → 𝟚)
    where

  record Commitment : ★ where
    constructor _,_
    field
      get-A get-B : G

  Challenge  = ℤq
  Response   = ℤq

  open ZK.Sigma-Protocol Commitment Challenge Response public

  record CipherText : ★ where
    constructor _,_
    field
      get-α get-β : G

  PubKey = G
  EncRnd = ℤq {- randomness used for encryption of ct -}
  Message = G {- plain text message -}

  enc : PubKey → EncRnd → Message → CipherText
  enc y r M = α , β where
    α = g ^ r
    β = (y ^ r) · M

  module _ (y : PubKey) (r : EncRnd) (w : ℤq) where
    prover-commitment : Commitment
    prover-commitment = (g ^ w) , (y ^ w)

    prover-response : Challenge → Response
    prover-response c = w + (r * c)

    prover : Prover
    prover = prover-commitment , prover-response

  module _ (y : PubKey) (M : Message) (ct : CipherText) where
    private
        α = CipherText.get-α ct
        β = CipherText.get-β ct
        β/M = β / M

    verifier : Verifier
    verifier (mk (A , B) c s)
      = (g ^ s) == (A · (α ^ c))
      ∧ (y ^ s) == (B · (β/M ^ c))

    -- This simulator shows why it is so important for the
    -- challenge to be picked once the commitment is known.
    
    -- To fake a transcript, the challenge and response can
    -- be arbitrarily chosen. However to be indistinguishable
    -- from a valid proof it they need to be picked at random.
    module _ (c : Challenge) (s : Response) where
        -- Compute A and B, such that the verifier accepts!
        private
            A = (g ^ s) / (α ^ c)
            B = (y ^ s) / (β/M ^ c)

        simulate-commitment : Commitment
        simulate-commitment = (A , B)

        simulate : Transcript
        simulate = mk simulate-commitment c s

        module Correct-simulation
           (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
           (/-·  : ∀ {P Q} → P ≡ (P / Q) · Q)
          where
          correct-simulation : ✓(verifier simulate)
          correct-simulation = ✓∧ (✓-== /-·) (✓-== /-·)

  module Correctness-proof
           (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
           (^-+  : ∀ {b x y} → b ^(x + y) ≡ (b ^ x) · (b ^ y))
           (^-*  : ∀ {b x y} → b ^(x * y) ≡ (b ^ x) ^ y)
           (·-/  : ∀ {P Q} → P ≡ (P · Q) / Q)
           (y : PubKey) (r : EncRnd) (w : ℤq) (M : Message) where
    open ≡-Reasoning

    correctness : Correctness (prover y r w)
                              (verifier y M (enc y r M))
    correctness c = ✓∧ (✓-== pf1) (✓-== pf2)
      where
        gʷ = g ^ w
        pf1 = g ^(w + (r * c))
            ≡⟨ ^-+ ⟩
              gʷ · (g ^(r * c))
            ≡⟨ ap (λ z → gʷ · z) ^-* ⟩
              gʷ · ((g ^ r) ^ c)
            ∎
        pf3 = y ^ (r * c)
            ≡⟨ ^-* ⟩
              (y ^ r)^ c
            ≡⟨ ap (λ b → b ^ c) ·-/ ⟩
              (((y ^ r) · M) / M) ^ c
            ∎
        pf2 = y ^(w + (r * c))
            ≡⟨ ^-+ ⟩
              (y ^ w) · (y ^(r * c))
            ≡⟨ ap (λ z → (y ^ w) · z) pf3 ⟩
             (y ^ w) · ((((y ^ r) · M) / M) ^ c)
            ∎
            

-- -}
-- -}
-- -}
-- -}
