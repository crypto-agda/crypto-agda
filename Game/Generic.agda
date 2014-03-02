{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Control.Protocol.CoreOld

module Game.Generic
  -- could be Public Key
  (Public    : ★)

  -- could be:
  --   * CPA:  Query _ = 𝟘
  --   * CCA2: Query _ = Ciphertext
  --   * CCA1: Query = [0: Ciphertext 1: 𝟘 ]
  (Query : 𝟚 → ★)

  -- could be:
  --   * CPA:  Response _ ()
  --   * CCA2: Response _ _ = Message
  --   * CCA1: Response 0₂ _ = Message
  --           Response 1₂ ()
  (Response : {i : 𝟚} → Query i → ★)

  -- could be:
  --   * CPA/CCA2/CCA1: ChallengeInput = Message × Message
  (ChallengeInput : ★)

  -- could be:
  --   * CPA/CCA2/CCA1: ChallengeOutput = Ciphertext
  --   * CCA2†: ChallengeOutput = Ciphertext × Ciphertext
  (ChallengeOutput : ★)

  (Guess : ★)
  where

Query₀ = Query 0₂
Query₁ = Query 1₂

module Challenger-proto where
    Round : (phase# : 𝟚) → Proto → Proto
    Round i = Server' (Query i) Response

    Round₀ = Round 0₂
    Round₁ = Round 1₂

    Challenge : Proto → Proto
    Challenge X = ChallengeInput →' (ChallengeOutput ×' X)

    End : Proto
    End = Guess →' end

    -- challenger implement this
    Main : Proto
    Main = Public ×' Round₀ (Challenge (Round₁ End))

module Adversary-proto where
    Round : (phase# : 𝟚) → Proto → Proto
    Round i = Client' (Query i) Response

    Round₀ = Round 0₂
    Round₁ = Round 1₂

    Challenge : Proto → Proto
    Challenge X = ChallengeInput ×' (ChallengeOutput →' X)

    End : Proto
    End = Guess ×' end

    Main : Proto
    Main = Public →' Round₀ (Challenge (Round₁ End))

module Proto-duality where
  module C = Challenger-proto
  module A = Adversary-proto
  proof : dual C.Main ≡ A.Main
  proof = refl

module Challenger-implementation
  -- could be Private Key
  (Private   : ★)

  -- could be 𝟚 for IND games
  (Secret    : ★)

  {- {OracleRand : {i : 𝟚} (q : Query i) → ★} -}
  (oracle    : Private → {i : 𝟚} (q : Query i) → {-OracleRand q →-} Response q)
  {ChalRand : ★}
  (challenge : Public → Secret → ChallengeInput → ChalRand → ChallengeOutput)
  where

    module _ (b : Secret)(pk : Public)(sk : Private)(chal-rand : ChalRand) where

      open Challenger-proto
      module _ {i : 𝟚}{A}(ContDone : A) where
        service : Server (Query i) Response A
        srv-ask  service q = oracle sk q {-{!!}-} , service
        srv-done service   = ContDone

      phase₁ : Server Query₁ Response (Guess → Guess)
      phase₁ = service id

      exchange : El Guess (Challenge (Round₁ (Guess →' end)))
      exchange m = challenge pk b m chal-rand , phase₁

      phase₀ : Server Query₀ Response (El Guess (Challenge (Round₁ (Guess →' end))))
      phase₀ = service exchange

      main : El Guess Main
      main = pk , phase₀

      main-com : El 𝟙 Adversary-proto.Main → Guess
      main-com = proj₁ ∘ com Main main
