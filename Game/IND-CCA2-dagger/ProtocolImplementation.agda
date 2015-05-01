{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product

open import Control.Protocol.CoreOld

open import Crypto.Schemes
import Game.IND-CCA2-dagger.Protocol

module Game.IND-CCA2-dagger.ProtocolImplementation
  (pke : Pubkey-encryption)
  where

open Pubkey-encryption pke
open Game.IND-CCA2-dagger.Protocol PubKey Message CipherText

module Challenger (b : 𝟚)(pk : PubKey)(sk : SecKey)(rₑ : Rₑ ²) where
  DecRound = Server CipherText (const (Maybe Message))

  module _ {X}(Cont : El 𝟙 X) where
    service : DecRound (El 𝟙 X)
    srv-ask  service q = dec sk q , service
    srv-done service   = Cont

  phase2 : DecRound 𝟙
  phase2 = service {end} _

  exchange : El 𝟙 (CCAChal (CCARound end))
  exchange m = (enc pk ∘ m ∘ flip _xor_ b ˢ rₑ) , phase2

  phase1 : DecRound (El 𝟙 (CCAChal (CCARound end)))
  phase1 = service {CCAChal (CCARound end)} exchange

CCA2d-Chal : (b : 𝟚)(rₖ : Rₖ)(rₑ : Rₑ ²) → El 𝟙 CCA2-dagger
CCA2d-Chal b rₖ rₑ with key-gen rₖ
... | pk , sk = pk , Challenger.phase1 b pk sk rₑ


{-
module Capture where
-- open Game.IND-CCA2-dagger.Adversary PubKey Message CipherText Rₐ
-- open Game.IND-CCA2-dagger.Experiment PubKey SecKey Message CipherText Rₑ Rₖ Rₐ key-gen enc dec
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
