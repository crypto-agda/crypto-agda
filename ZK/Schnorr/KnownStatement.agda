open import Type using (Type)
open import Function using (flip)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; idp; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import ZK.Types using (Cyclic-group; module Cyclic-group
                           ; Cyclic-group-properties; module Cyclic-group-properties)
import ZK.SigmaProtocol.KnownStatement

module ZK.Schnorr.KnownStatement
    {G ℤq : Type}
    (cg : Cyclic-group G ℤq)
    (y : G)
    where
  open Cyclic-group cg

  Commitment = G
  Challenge  = ℤq
  Response   = ℤq
  Witness    = ℤq
  Randomness = ℤq
  _∈y : Witness → Type
  x ∈y = g ^ x ≡ y

  open ZK.SigmaProtocol.KnownStatement Commitment Challenge Response Randomness Witness _∈y public

  prover : Prover
  prover a x = (g ^ a) , response
     where response : Challenge → Response
           response c = (a + (x * c))

  verifier : Verifier
  verifier (mk A c s) = (g ^ s) == (A · (y ^ c))

  Schnorr : Σ-Protocol
  Schnorr = (prover , verifier)

  -- The simulator shows why it is so important for the
  -- challenge to be picked once the commitment is known.
  -- To fake a transcript, the challenge and response can
  -- be arbitrarily chosen. However to be indistinguishable
  -- from a valid proof they need to be picked at random.
  simulator : Simulator
  simulator c s = A
      where
        -- Compute A, such that the verifier accepts!
        A = (g ^ s) / (y ^ c)

  -- The extractor shows the importance of never reusing a
  -- commitment. If the prover answers to two different challenges
  -- comming from the same commitment then the knowledge of the
  -- prover (the witness) can be extracted.
  extractor : Extractor verifier
  extractor t² = x'
      module Witness-extractor where
        open Transcript² t²
        fd = get-f₀ - get-f₁
        cd = get-c₀ - get-c₁
        x' = fd * modinv cd
  
  module Proofs (cg-props : Cyclic-group-properties cg) where
    open Cyclic-group-properties cg-props
    open ≡-Reasoning

    correct : Correct Schnorr
    correct x a c w -- rewrite ! w
      = ✓-== (g ^(a + (x * c))
           ≡⟨ ^-+ ⟩
              A · (g ^(x * c))
           ≡⟨ ap (λ z → A · z) ^-* ⟩
              A · ((g ^ x) ^ c)
           ≡⟨ ap (λ z → A · (z ^ c)) w ⟩
              A · (y ^ c)
           ∎)
      where
        A = g ^ a

    shvzk : Special-Honest-Verifier-Zero-Knowledge Schnorr
    shvzk = record { simulator = simulator
                   ; correct-simulator = λ _ _ → ✓-== /-· }

    module _ (t² : Transcript² verifier) where
      private
        x  = dlog g y

      open Transcript² t² renaming (get-A to A; get-c₀ to c₀; get-c₁ to c₁
                                   ;get-f₀ to f₀; get-f₁ to f₁)
      open Witness-extractor t²

      .g^xcd≡g^fd : _
      g^xcd≡g^fd = g ^(x * cd)
                 ≡⟨ ^-* ⟩
                   (g ^ x) ^ (c₀ - c₁)
                 ≡⟨ ap₂ _^_ (dlog-ok g y) idp ⟩
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
      .extractor-ok : g ^ x' ≡ y 
      extractor-ok = ! ap (_^_ g) (left-*-to-right-/ (^-inj g^xcd≡g^fd)) ∙ dlog-ok g y

    special-soundness : Special-Soundness Schnorr
    special-soundness = record { extractor = extractor
                               ; extract-valid-witness = extractor-ok }

    special-Σ-protocol : Special-Σ-Protocol
    special-Σ-protocol = record { Σ-protocol = Schnorr ; correct = correct ; shvzk = shvzk ; ssound = special-soundness }
-- -}
-- -}
-- -}
-- -}
