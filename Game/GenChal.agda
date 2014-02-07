{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Product

open import Control.Protocol.Core

module Game.GenChal
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
  --   * CPA/CCA2/CCA1: Challenge = Ciphertext
  --   * CCA2†: Challenge = Ciphertext × Ciphertext
  (Challenge : ★)

  (ContProto : Proto)
  where

Query₀ = Query 0₂
Query₁ = Query 1₂

Round : (phase# : 𝟚) → Proto → Proto
Round i = Server' (Query i) Response

Round₀ = Round 0₂
Round₁ = Round 1₂

Chal : Proto → Proto
Chal X = ChallengeInput →' (Challenge ×' X)

-- challenger implement this
Main : Proto
Main = Public ×' Round₀ (Chal (Round₁ ContProto))

module Implementation
  -- could be Private Key
  (Private   : ★)

  -- could be 𝟚 for IND games
  (Secret    : ★)

  {X}
  (cont      : El X ContProto)

  {- {OracleRand : {i : 𝟚} (q : Query i) → ★} -}
  (oracle    : Private → {i : 𝟚} (q : Query i) → {-OracleRand q →-} Response q)
  {ChalRand : ★}
  (challenge : Public → Secret → ChallengeInput → ChalRand → Challenge)
  where

    module _ (b : Secret)(pk : Public)(sk : Private)(chal-rand : ChalRand) where

      module _ {i : 𝟚}{A}(ContDone : A) where
        service : Server (Query i) Response A
        srv-ask  service q = oracle sk q {-{!!}-} , service
        srv-done service   = ContDone

      phase₁ : Server Query₁ Response (El X ContProto)
      phase₁ = service cont

      exchange : El X (Chal (Round₁ ContProto))
      exchange m = challenge pk b m chal-rand , phase₁

      phase₀ : Server Query₀ Response (El X (Chal (Round₁ ContProto)))
      phase₀ = service exchange

      main : El X Main
      main = pk , phase₀
