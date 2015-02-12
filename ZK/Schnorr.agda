open import Type using (Type)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; idp; ap; ap₂; !_; _∙_; module ≡-Reasoning)
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
  Witness    = ℤq
  Randomness = ℤq
  Statement  = G
  _∈_ : Witness → Statement → Type
  x ∈ y = g ^ x ≡ y

  open ZK.SigmaProtocol Commitment Challenge Response Randomness Witness Statement _∈_

  prover : Prover
  prover a x _y = (g ^ a) , response
     where response : Challenge → Response
           response c = (a + (x * c))

  verifier : Verifier
  verifier y (mk A c s) = (g ^ s) == (A · (y ^ c))

  -- This simulator shows why it is so important for the
  -- challenge to be picked once the commitment is known.

  -- To fake a transcript, the challenge and response can
  -- be arbitrarily chosen. However to be indistinguishable
  -- from a valid proof they need to be picked at random.
  simulator : Simulator
  simulator y c s = A
      where
        -- Compute A, such that the verifier accepts!
        A = (g ^ s) / (y ^ c)

  extractor : Extractor verifier
  extractor y t² = x
      module Witness-extractor where
        open Transcript² t²
        fd = get-f₀ - get-f₁
        cd = get-c₀ - get-c₁
        x  = fd * modinv cd

  Schnorr : Σ-Protocol
  Schnorr = (prover , verifier)
  
  module Proofs (cg-props : Cyclic-group-properties cg)
                -- TODO move dlog and dlog-ok in Cyclic-group-properties but beware it is not computable
                (dlog : G → ℤq) 
                (dlog-ok : (y : G) → g ^ dlog y ≡ y) where
    open Cyclic-group-properties cg-props

    correct : Correct Schnorr
    correct a {x} {y} c w rewrite ! w
      = ✓-== (g ^(a + (x * c))
           ≡⟨ ^-+ ⟩
              gᵃ · (g ^(x * c))
           ≡⟨ ap (λ z → gᵃ · z) ^-* ⟩
              gᵃ · ((g ^ x) ^ c)
           ∎)
      where
        open ≡-Reasoning
        gᵃ = g ^ a

    shvzk : Special-Honest-Verifier-Zero-Knowledge Schnorr
    shvzk = record { simulator = simulator
                   ; correct-simulator = λ _ _ _ → ✓-== /-· }

    module _ (y : G) (t² : Transcript² verifier y) where
      private
        x  = dlog y
        x' = extractor y t²

      open Transcript² t² renaming (get-A to A; get-c₀ to c₀; get-c₁ to c₁
                                   ;get-f₀ to f₀; get-f₁ to f₁)
      open Witness-extractor y t² hiding (x)
      open ≡-Reasoning

      g^xcd≡g^fd = g ^(x * cd)
                 ≡⟨ ^-* ⟩
                   (g ^ x) ^ (c₀ - c₁)
                 ≡⟨ ap₂ _^_ (dlog-ok y) idp ⟩
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
      extractor-ok : g ^ x' ≡ y 
      extractor-ok = ! ap (_^_ g) (left-*-to-right-/ (^-inj g^xcd≡g^fd)) ∙ dlog-ok y

    special-soundness : Special-Soundness Schnorr
    special-soundness = record { extractor = extractor
                               ; extract-valid-witness = extractor-ok }
-- -}
-- -}
-- -}
-- -}
