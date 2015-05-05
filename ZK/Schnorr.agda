open import Type using (Type)
open import Function using (flip)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; idp; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import ZK.Types using (Cyclic-group; module Cyclic-group)
import ZK.SigmaProtocol

module ZK.Schnorr
    {G ℤq : Type}
    (cg : Cyclic-group G ℤq)
    where
  open Cyclic-group cg

  Statement  = G
  Commitment = G
  Challenge  = ℤq
  Response   = ℤq
  Witness    = ℤq
  Randomness = ℤq
  _∈_ : Witness → Statement → Type
  x ∈ y = g ^ x ≡ y

  open ZK.SigmaProtocol Statement (λ _ → Commitment) (λ _ → Challenge) (λ _ → Response) (λ _ → Randomness) (λ _ → Witness) (flip _∈_)

  import ZK.Schnorr.KnownStatement cg as KS

  prover : Prover
  prover = KS.prover

  verifier : Verifier
  verifier = KS.verifier

  Schnorr : Σ-Protocol
  Schnorr = (prover , verifier)

  simulator : Simulator
  simulator = KS.simulator

  extractor : Extractor verifier
  extractor = KS.extractor
  
  correct : Correct Schnorr
  correct = KS.correct

  shvzk : Special-Honest-Verifier-Zero-Knowledge Schnorr
  shvzk = record { simulator = simulator
                 ; correct-simulator = λ _ _ _ → ≡⇒== /-· }

  special-soundness : Special-Soundness Schnorr
  special-soundness = record { extractor = extractor
                             ; extract-valid-witness = KS.extractor-ok }

  special-Σ-protocol : Special-Σ-Protocol
  special-Σ-protocol = record { Σ-protocol = Schnorr ; correct = correct ; shvzk = shvzk ; ssound = special-soundness }

{-
OLDER version, not using Schnorr.KnownStatement

  prover : Prover
  prover _y a x = (g ^ a) ZK.SigmaProtocol., response -- TODO Internal error in Agda if one leaves the constructor unqualified
     where response : Challenge → Response
           response c = (a + (x * c))

  verifier : Verifier
  verifier y (mk A c s) = (g ^ s) == (A · (y ^ c))

  Schnorr : Σ-Protocol
  Schnorr = (prover , verifier)

  -- The simulator shows why it is so important for the
  -- challenge to be picked once the commitment is known.
  -- To fake a transcript, the challenge and response can
  -- be arbitrarily chosen. However to be indistinguishable
  -- from a valid proof they need to be picked at random.
  simulator : Simulator
  simulator y c s = A
      where
        -- Compute A, such that the verifier accepts!
        A = (g ^ s) / (y ^ c)

  -- The extractor shows the importance of never reusing a
  -- commitment. If the prover answers to two different challenges
  -- comming from the same commitment then the knowledge of the
  -- prover (the witness) can be extracted.
  extractor : Extractor verifier
  extractor y t² = x'
      module Witness-extractor where
        open Transcript² y t²
        fd = get-f₀ − get-f₁
        cd = get-c₀ − get-c₁
        x' = fd * cd ⁻¹
  
  open ≡-Reasoning

  correct : Correct Schnorr
  correct y x a c w rewrite ! w
    = ≡⇒== (g ^(a + (x * c))
         ≡⟨ ^-+ ⟩
            gᵃ · (g ^(x * c))
         ≡⟨ ap (λ z → gᵃ · z) ^-* ⟩
            gᵃ · ((g ^ x) ^ c)
         ∎)
    where
      gᵃ = g ^ a

  shvzk : Special-Honest-Verifier-Zero-Knowledge Schnorr
  shvzk = record { simulator = simulator
                 ; correct-simulator = λ _ _ → ≡⇒== /-· }

  module _ (y : G) (t² : Transcript² verifier y) where
    private
      x  = dlog y

    open Transcript² y t² renaming (get-A to A; get-c₀ to c₀; get-c₁ to c₁
                                   ;get-f₀ to f₀; get-f₁ to f₁)
    open Witness-extractor y t²

    .g^xcd≡g^fd : _
    g^xcd≡g^fd = g ^(x * cd)
               ≡⟨ ^-* ⟩
                 (g ^ x) ^ (c₀ − c₁)
               ≡⟨ ap₂ _^_ (dlog-ok y) idp ⟩
                 y ^ (c₀ − c₁)
               ≡⟨ ^-- ⟩
                 (y ^ c₀) / (y ^ c₁)
               ≡⟨ ! cancels-/ ⟩
                 (A · (y ^ c₀)) / (A · (y ^ c₁))
               ≡⟨ ap₂ _/_ (! ==⇒≡ verify₀) (! ==⇒≡ verify₁) ⟩
                 (g ^ f₀) / (g ^ f₁)
               ≡⟨ ! ^-- ⟩
                 g ^ fd
               ∎

    -- The extracted x is correct
    .extractor-ok : g ^ x' ≡ y
    extractor-ok = ! ap (_^_ g) (left-*-to-right-/ (^-inj g^xcd≡g^fd)) ∙ dlog-ok y

  special-soundness : Special-Soundness Schnorr
  special-soundness = record { extractor = extractor
                             ; extract-valid-witness = extractor-ok }

  special-Σ-protocol : Special-Σ-Protocol
  special-Σ-protocol = record { Σ-protocol = Schnorr ; correct = correct ; shvzk = shvzk ; ssound = special-soundness }
-- -}
-- -}
-- -}
-- -}
