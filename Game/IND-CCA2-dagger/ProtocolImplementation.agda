
{-# OPTIONS --copatterns #-}

open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product

open import Data.Nat.NP
--open import Rat

open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open Operators
open import Control.Strategy renaming (run to runStrategy)
open import Control.Protocol.CoreOld
open import Game.Challenge
import Game.IND-CPA-utils

import Game.IND-CCA2-dagger.Adversary
import Game.IND-CCA2-dagger.Valid
import Game.IND-CCA2-dagger.Experiment
import Game.IND-CCA2-dagger.Protocol

open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2-dagger.ProtocolImplementation
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)

  where

open Game.IND-CCA2-dagger.Protocol PubKey Message CipherText

module Challenger (b : 𝟚)(pk : PubKey)(sk : SecKey)(rₑ : Rₑ ²) where

  module _ {X}(Cont : El 𝟙 X) where
    service : Server CipherText (const Message) (El 𝟙 X)
    srv-ask  service q = (Dec sk q) , service
    srv-done service   = Cont

  phase2 : Server CipherText (const Message) 𝟙
  phase2 = service {end} _

  exchange : El 𝟙 (CCAChal (CCARound end))
  exchange m = (Enc pk ∘ m ∘ flip _xor_ b ˢ rₑ) , phase2

  phase1 : Server CipherText (const Message) (El 𝟙 (CCAChal (CCARound end)))
  phase1 = service {CCAChal (CCARound end)} exchange


CCA2d-Chal : (b : 𝟚)(rₖ : Rₖ)(rₑ : Rₑ ²) → El 𝟙 CCA2-dagger
CCA2d-Chal b rₖ rₑ with KeyGen rₖ
... | pk , sk = pk , Challenger.phase1 b pk sk rₑ


{-
module Capture where
-- open Game.IND-CCA2-dagger.Adversary PubKey Message CipherText Rₐ
-- open Game.IND-CCA2-dagger.Experiment PubKey SecKey Message CipherText Rₑ Rₖ Rₐ KeyGen Enc Dec
  open Game.IND-CPA-utils

  chal : ChalAdversary (Message ²) (CipherText ²)
           (DecRound Message CipherText 𝟚)
       → Message ² × (CipherText ² →
           Client CipherText (const Message) 𝟚)
  chal chal = get-chal chal , (λ cs → put-resp chal cs)

  phase1 : DecRound Message CipherText
            (ChalAdversary (Message ²) (CipherText ²)
            (DecRound Message CipherText 𝟚))
         → Client CipherText (const Message)
            (Message ² × (CipherText ² →
            Client CipherText (const Message) 𝟚))
  phase1 (ask q? cont) = ask q? (λ r → phase1 (cont r))
  phase1 (done x) = done (chal x)

  transform : Adversary → Rₐ → El 𝟚 (dual CCA2-dagger)
  transform adv rₐ pk = phase1 (adv rₐ pk)

module Capture-com (b : 𝟚)(A : Adversary)(rₐ : Rₐ)(rₖ : Rₖ)(rₑ₀ rₑ₁ : Rₑ) where

{-
  proof : (_ , EXP b A (rₐ , rₖ , rₑ₀ , rₑ₁))
        ≡ com CCA2-dagger (CCA2d-Chal b rₖ [0: rₑ₀ 1: rₑ₁ ]) (Capture.transform A rₐ)
  proof = {!!}
-}

-}
