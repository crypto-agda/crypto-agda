{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.Two
open import Data.Product
open import Data.Maybe
open import Data.Nat
open import Data.Vec hiding (_>>=_ ; _∈_)
-- open import Data.List as L
open import Data.Fin as Fin using (Fin)
open import Control.Strategy renaming (map to mapS)
open import Control.Strategy.Utils
open import Game.Challenge
import Game.ReceiptFreeness.Adversary
import Game.IND-CCA2-dagger.Adversary
import Game.IND-CPA-utils

import Data.List.Any
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

module Game.Transformation.ReceiptFreeness-CCA2d.Simulator
  (PubKey    : Type)
  (CipherText : Type)

  (SerialNumber² : Type)
  (Receipt : Type)
  (MarkedReceipt? : Type)
  (Ballot : Type)
  (Tally : Type)
  (BB    : Type)
  ([]    : BB)
  (_∷_ : Receipt → BB → BB)
  (Rgb   : Type)
  (genBallot : PubKey → Rgb → Ballot)
  (tallyMarkedReceipt? : let CO = 𝟚 in CO → MarkedReceipt? → Tally)
  (0,0   : Tally)
  (1,1   : Tally)
  (_+,+_ : Tally → Tally → Tally)
  (receipts : SerialNumber² → CipherText ² → Receipt ²)
  (enc-co : Receipt → CipherText)
  (m?     : Receipt → MarkedReceipt?)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₐ : Type)
  (#q : ℕ) (max#q : Fin #q)
  (Check    : BB → Receipt → 𝟚)
  (Message : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  where

_∷²_ : Receipt ² → BB → BB
r ∷² xs = r 0₂ ∷ (r 1₂ ∷ xs)

CO = 𝟚
Candidate = 𝟚

open Game.IND-CPA-utils Message CipherText
module RFA = Game.ReceiptFreeness.Adversary PubKey SerialNumber² Rₐ Receipt Ballot Tally CO BB
open RFA renaming (Phase to RFPhase; Q to RFQ; Resp to RFResp)

Rₐ† : Type
Rₐ† = Rₐ × (Vec Rgb #q)²

module CCA2† = Game.IND-CCA2-dagger.Adversary PubKey Message CipherText Rₐ†

CCAProto : Proto
CCAProto = P[ CipherText , const (Maybe Message) ]

RFProto : Proto
RFProto = P[ RFQ , RFResp ]

MITMState : Type → Type
MITMState X = X × BB × Tally

module Simulator (RFA : Adversary) where
  module SecondLayer (rgb : (Vec Rgb #q)²) (pk : PubKey) where
    open MITM

    ballot : PhaseNumber → Fin #q → Ballot
    ballot p# n = genBallot pk (lookup n (rgb p#))

    MITM-phase : (p# : PhaseNumber) → Fin #q → BB → Tally → ∀ {X} → MITM {CCAProto} {RFProto} {MITMState X}
    MITM-phase-vote : ∀ v (p# : PhaseNumber) → Fin #q → BB → Tally → 𝟚 → ∀ {X}
       → Client CCAProto (P'.R {CCAProto} {RFProto} {MITMState X}{X} (Vote v) × MITM {CCAProto} {RFProto} {MITMState X} {X})
    hack-query (MITM-phase p# n bb ta) REB = done (ballot p# n , MITM-phase p# (Fin.pred n) bb ta)
    hack-query (MITM-phase p# n bb ta) RBB = done (bb , MITM-phase p# (Fin.pred n) bb ta)
    hack-query (MITM-phase p# n bb ta) RTally = done (ta , MITM-phase p# (Fin.pred n) bb ta)
    hack-query (MITM-phase p# n bb ta) (RCO r) =
       -- if receipt in DB then ...
       ask (enc-co r) λ mco → done (Message→𝟚 mco , MITM-phase p# (Fin.pred n) bb ta)
    hack-query (MITM-phase p# n bb ta) (Vote v) = MITM-phase-vote v p# n bb ta (Check bb v)
    hack-result (MITM-phase p# n bb ta) r = done (r , bb , ta)

    MITM-phase-vote _ p# n bb ta 0₂ = done (reject , MITM-phase p# (Fin.pred n) bb ta)
    MITM-phase-vote r p# n bb ta 1₂ = ask (enc-co r) λ mco →
      let co = Message→𝟚 mco in
      done (accept , MITM-phase p# (Fin.pred n) (r ∷ bb) (tallyMarkedReceipt? co (m? r) +,+ ta))

    MITM-RFChallenge : ∀ {X} → MITM {_} {_} {MITMState X}
    MITM-RFChallenge = MITM-phase 0₂ max#q [] 0,0

    hack-challenge : ∀ {X} → RFChallenge X → CPA†Adversary (X × Receipt ²)
    get-chal (hack-challenge _)     = 𝟚→Message
    put-resp (hack-challenge rfc) c = put-resp rfc rec , rec
      where rec = receipts (get-chal rfc) c

    module _ (bb : BB) (ta : Tally) (Aphase2 : RFPhase Candidate) where

      decRoundAdv2 : DecRound (MITMState Candidate)
      decRoundAdv2 = mitm-to-client-trans (MITM-phase 1₂ max#q bb ta) Aphase2

    mapCPAAdv = Map.A*

    A†3 : BB → Tally → (RFPhase Candidate × Receipt ²) → DecRound Candidate
    A†3 bb ta (phase2 , r) = mapS proj₁ (decRoundAdv2 (r ∷² bb) (1,1 +,+ ta) phase2)

    A†2 : MITMState (RFChallenge (RFPhase Candidate)) → CPA†Adversary (DecRound Candidate)
    A†2 (rfc , bb , ta) = mapCPAAdv id id (A†3 bb ta) (hack-challenge rfc)

  module AdversaryParts (rgb : (Vec Rgb #q)²) (pk : PubKey) (rₐ : Rₐ) where
    open SecondLayer rgb pk public
    A†1 : Client CCAProto (MITMState (RFChallenge (RFPhase Candidate)))
    A†1 = mitm-to-client-trans MITM-RFChallenge (RFA rₐ pk)

  A† : CCA2†.Adversary
  A† (rₐ , rgb) pk = mapS A†2 A†1
     where open AdversaryParts rgb pk rₐ

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
