open import Type using (Type)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; idp; ap; ap₂; !_; module ≡-Reasoning)
open import ZK.Types using (Cyclic-group; module Cyclic-group
                           ; Cyclic-group-properties; module Cyclic-group-properties)
import ZK.SigmaProtocol

module ZK.Schnorr
    {G ℤq : Type}
    (cg : Cyclic-group G ℤq)
    where
  open Cyclic-group cg

  Commitment = G
  Challenge  = ℤq
  Response   = ℤq

  open ZK.SigmaProtocol Commitment Challenge Response

  module _ (x a : ℤq) where
    prover-commitment : Commitment
    prover-commitment = g ^ a

    prover-response : Challenge → Response
    prover-response c = a + (x * c)

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
    simulator : Simulator
    simulator c s = A
      where
        -- Compute A, such that the verifier accepts!
        A = (g ^ s) / (y ^ c)

    witness-extractor : Transcript² verifier → ℤq
    witness-extractor t² = x
      module Witness-extractor where
        open Transcript² t²
        fd = get-f₀ - get-f₁
        cd = get-c₀ - get-c₁
        x  = fd * modinv cd

    extractor : ∀ a → Extractor verifier
    extractor a t² = prover (witness-extractor t²) a

  Schnorr : ∀ x a → Σ-Protocol
  Schnorr x a = (prover x a , let y = g ^ x in verifier y)
  
  module Proofs (cg-props : Cyclic-group-properties cg) where
    open Cyclic-group-properties cg-props

    correct : ∀ x a → Correct (Schnorr x a)
    correct x a c
      = ✓-== (g ^(a + (x * c))
           ≡⟨ ^-+ ⟩
              gʷ · (g ^(x * c))
           ≡⟨ ap (λ z → gʷ · z) ^-* ⟩
              gʷ · (y ^ c)
           ∎)
      where
        open ≡-Reasoning
        gʷ = g ^ a
        y  = g ^ x

    shvzk : ∀ x a → Special-Honest-Verifier-Zero-Knowledge (Schnorr x a)
    shvzk x a = record { simulator = simulator y
                     ; correct-simulator = λ _ _ → ✓-== /-· }
      where y = g ^ x

    module _ (x : ℤq) (t² : Transcript² (verifier (g ^ x))) where
      private
        y = g ^ x
        x' = witness-extractor y t²

      open Transcript² t² renaming (get-A to A; get-c₀ to c₀; get-c₁ to c₁
                                   ;get-f₀ to f₀; get-f₁ to f₁)
      open Witness-extractor y t² hiding (x)
      open ≡-Reasoning

      g^xcd≡g^fd = g ^(x * cd)
                 ≡⟨ ^-* ⟩
                   y ^ (c₀ - c₁)
                 ≡⟨ ^-- ⟩
                   (y ^ c₀) / (y ^ c₁)
                 ≡⟨ ! cancels-/ ⟩
                   (A · (y ^ c₀)) / (A · (y ^ c₁))
                 ≡⟨ ap₂ _/_ (! ==-✓ verify₀) (! ==-✓ verify₁) ⟩
                   (g ^ f₀) / (g ^ f₁)
                 ≡⟨ ! ^-- ⟩
                   g ^ fd
                 ∎

      -- The extracted x is correct
      x≡x' : x ≡ x'
      x≡x' = left-*-to-right-/ (^-inj g^xcd≡g^fd)

      extractor-exact : ∀ a → EqProver (extractor y a t²) (prover x a)
      extractor-exact a = idp , (λ c → ap (λ z → _+_ a (_*_ z c)) (! x≡x'))

    special-soundness : ∀ x a → Special-Soundness (Schnorr x a)
    special-soundness x a = record { extractor = extractor y a
                                 ; extractor-exact = λ t² → extractor-exact x t² a }
       where y = g ^ x
-- -}
-- -}
-- -}
-- -}
