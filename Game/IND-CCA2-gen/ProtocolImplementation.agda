{-# OPTIONS --copatterns #-}
open import Type
open import Data.Two
open import Data.One
open import Data.Product
import Game.IND-CCA2-gen.Protocol

open import Control.Protocol.Core

module Game.IND-CCA2-gen.ProtocolImplementation
  -- could be Secret Key
  (Secret     : ★)
  -- could be Public Key
  (Public     : ★)
  -- could be Ciphertext
  (Query : ★)
  -- could be Message
  (Response : Query → ★)
  -- could be Ciphertext or pair of Ciphertext in CCA2-dagger
  (Challenge : ★)
  -- could be a pair of Messages or unit if no input required
  (ChallengeInput : ★)
  (oracle : Secret → (q : Query) → Response q)
  (challenge : Public  → 𝟚 → ChallengeInput → Challenge)
  where

open Game.IND-CCA2-gen.Protocol Public  Query Response Challenge ChallengeInput

module Challenger (b : 𝟚)(pk : Public )(sk : Secret) where

  module _ {A}(Cont : A) where
    service : Server Query Response A
    srv-ask  service q = oracle sk q , service
    srv-done service   = Cont

  phase2 : Server Query Response 𝟙
  phase2 = service _

  exchange : El 𝟙 (CCAChal (CCARound end))
  exchange m = challenge pk b m , phase2

  phase1 : Server Query Response (El 𝟙 (CCAChal (CCARound end)))
  phase1 = service exchange

CCA2g-Chal : (b : 𝟚)(pk : Public)(sk : Secret) → El 𝟙 CCA2-gen
CCA2g-Chal b pk sk = pk , Challenger.phase1 b pk sk

-- -}
-- -}
-- -}
