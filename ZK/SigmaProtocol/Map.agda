{-# OPTIONS --without-K #-}
open import Function
open import Type                 using (Type; Type₁)
open import Data.Bool.Base       using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP
open import ZK.SigmaProtocol.Signature
open import ZK.SigmaProtocol.Structure
import ZK.SigmaProtocol.KnownStatement as ΣPKS

module ZK.SigmaProtocol.Map where

record W-Map
         {W₀ : Type}(V₀ : W₀ → Type)
         {W₁ : Type}(V₁ : W₁ → Type) : Type where
  field
    →Witness : W₀ → W₁
    ←Witness : W₁ → W₀
    →Valid   : ∀ {w₀}(w₀? : V₀ w₀) → V₁ (→Witness w₀)
    ←Valid   : ∀ {w₁}(w₁? : V₁ w₁) → V₀ (←Witness w₁)

module Apply-W-Map
         {W₀ : Type}{V₀ : W₀ → Type}
         {W₁ : Type}{V₁ : W₁ → Type}
         (W-map : W-Map V₀ V₁)
         (σ₀ : Σ-Structure V₀)
         where
  open W-Map W-map
  module σ₀ = Σ-Structure σ₀
  open Σ-Signature σ₀.Σ-sig
  module Σ₁ = ΣPKS Commitment Challenge Response Randomness W₁ V₁

  prover : Σ₁.Prover
  prover r = σ₀.prover r ∘ ←Witness

  Σ-protocol : Σ₁.Σ-Protocol
  Σ-protocol = prover Σ₁., σ₀.verifier

  module Σ-protocol = Σ₁.Σ-Protocol Σ-protocol

  extractor : Σ₁.Extractor σ₀.verifier
  extractor = →Witness ∘ σ₀.extractor

  .correct : Σ₁.Correct Σ-protocol
  correct w₁ r₁ c₁ w₁? = σ₀.correct (←Witness w₁) r₁ c₁ (←Valid w₁?)

  shvzk : Σ₁.Special-Honest-Verifier-Zero-Knowledge Σ-protocol
  shvzk = record { correct-simulator = σ₀.correct-simulator }

  .extract-valid-witness : Σ₁.Extract-Valid-Witness σ₀.verifier extractor
  extract-valid-witness = →Valid ∘ σ₀.extract-valid-witness

  special-soundness : Σ₁.Special-Soundness Σ-protocol
  special-soundness = record { extract-valid-witness = extract-valid-witness }

  special-Σ-protocol : Σ₁.Special-Σ-Protocol
  special-Σ-protocol = record { correct = correct
                              ; shvzk = shvzk
                              ; ssound = special-soundness }

  Σ-structure : Σ-Structure V₁
  Σ-structure = record { special-Σ-protocol = special-Σ-protocol }

{-

record Σ-Map {W₀ : Type}{V₀ : W₀ → Type}(Σ₀ : Σ-Signature V₀)
             {W₁ : Type}{V₁ : W₁ → Type}(Σ₁ : Σ-Signature V₁) : Type where
  module Σ₀ = Σ-Signature Σ₀
  module Σ₁ = Σ-Signature Σ₁
  field
    →Witness    : W₀ → W₁
    ←Witness    : W₁ → W₀
    ←Valid      : ∀ {w₁}(w₁? : V₁ w₁) → V₀ (←Witness w₁) 
    ←Randomness : Σ₁.Randomness → Σ₀.Randomness
    →Commitment : Σ₀.Commitment → Σ₁.Commitment
    ←Commitment : Σ₁.Commitment → Σ₀.Commitment
    ←Challenge  : Σ₁.Challenge  → Σ₀.Challenge
    -- →Challenge  : Σ₀.Challenge  → Σ₁.Challenge
    →Response   : Σ₀.Response   → Σ₁.Response
    ←Response   : Σ₁.Response   → Σ₀.Response

    ←Challenge-inj : ∀ {c₀ c₁} → ←Challenge c₀ ≡ ←Challenge c₁ → c₀ ≡ c₁
module Apply-Σ-Map
         {W₀ : Type}{V₀ : W₀ → Type}{Σ₀ : Σ-Signature V₀}
         {W₁ : Type}{V₁ : W₁ → Type}{Σ₁ : Σ-Signature V₁}
         (Σ-map : Σ-Map Σ₀ Σ₁)
         (σ₀ : Σ-Structure Σ₀)
         where
  open Σ-Map Σ-map
  module σ₀ = Σ-Structure σ₀

  prover : Σ₁.Prover
  prover r w = A₁ Σ₁., f₁ where
    module P₀ = σ₀.Prover-Interaction (σ₀.prover (←Randomness r) (←Witness w))
    A₁ = →Commitment P₀.get-A
    f₁ = →Response ∘ P₀.get-f ∘ ←Challenge

  verifier : Σ₁.Verifier
  verifier (Σ₁.mk A c f) = σ₀.verifier (Σ₀.mk (←Commitment A) (←Challenge c) (←Response f))

  Σ-protocol : Σ₁.Σ-Protocol
  Σ-protocol = prover Σ₁., verifier

  module Σ-protocol = Σ₁.Σ-Protocol Σ-protocol

  simulator : Σ₁.Simulator
  simulator c s = →Commitment (σ₀.simulator (←Challenge c) (←Response s))

  extractor : Σ₁.Extractor verifier
  extractor t² = →Witness (σ₀.extractor (Σ₀.mk A c₀ c₁ c₀≢c₁ f₀ f₁ t².verify₀ t².verify₁))
    where
      module t² = Σ₁.Transcript² t²
      A  = ←Commitment t².get-A
      c₀ = ←Challenge  t².get-c₀
      c₁ = ←Challenge  t².get-c₁
      c₀≢c₁ : c₀ ≢ c₁
      c₀≢c₁ = t².c₀≢c₁ ∘ ←Challenge-inj
      f₀ = ←Response t².get-f₀
      f₁ = ←Response t².get-f₁

{-
  .correct : Σ₁.Correct Σ-protocol
  correct w₁ r₁ c₁ w₁? = {!p₀!}
    where
      w₀ = ←Witness w₁
      r₀ = ←Randomness r₁
      c₀ = ←Challenge c₁
      p₀ = σ₀.correct w₀ r₀ c₀ (←Valid w₁?)

  shvzk : Σ₁.Special-Honest-Verifier-Zero-Knowledge Σ-protocol
  shvzk = record { simulator = simulator ; correct-simulator = {!!} }

  special-soundness : Σ₁.Special-Soundness Σ-protocol
  special-soundness = record { extractor = extractor ; extract-valid-witness = {!!} }

  special-Σ-protocol : Σ₁.Special-Σ-Protocol
  special-Σ-protocol = record { Σ-protocol = Σ-protocol
                              ; correct = correct
                              ; shvzk = shvzk
                              ; ssound = special-soundness }

  Σ-structure : Σ-Structure Σ₁
  Σ-structure = record { special-Σ-protocol = special-Σ-protocol }
  
-- -}
-- -}
-- -}
-- -}
