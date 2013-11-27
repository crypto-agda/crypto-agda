open import Function
open import Type
open import Data.Fin as Fin
open import Data.Nat.NP using (ℕ)
open import Data.Two
open import Data.Product
import Data.List as L
open L using (_∷_ ; [])
open import Data.Vec

import Data.List.Any as LA

open import Game.Challenge
open import Control.Strategy

open import Relation.Binary.PropositionalEquality.NP as ≡

open module M {X : ★} = LA.Membership (≡.setoid X)

import Game.ReceiptFreeness.Definitions as RF

module Game.ReceiptFreeness.Experiment
  (PubKey    : ★)
  (SecKey    : ★)
  -- Message = 𝟚
  (CipherText : ★)

  (SerialNumber : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  (#q : ℕ) (max#q : Fin #q)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : let Message = 𝟚 in
            PubKey → Message → Rₑ → CipherText)
  (Dec    : let Message = 𝟚 in
            SecKey → CipherText → Message)
  (Check : let open RF PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec
            in BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → proj₁ (proj₂ r) ∉ L.map (proj₁ ∘ proj₂) bb)
  where

open RF PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec
  
module Oracle (sk : SecKey) (pk : PubKey) (rgb : Rgb) (bb : BB) where
    resp : (q : Q) → Resp q
    resp REB = genBallot pk rgb
    resp RBB = bb
    resp RTally = tally sk bb
    resp (RCO (_ , _ , receipt)) = Dec sk receipt
    -- do we check if the sn is already here?
    resp (Vote v) = [0: reject 1: accept ]′ (Check bb v)

    newBB : Q → BB
    newBB (Vote v) = [0: bb 1: v ∷ bb ]′ (Check bb v)
    newBB _ = bb

private
  State : (S A : ★) → ★
  State S A = S → A × S
open StatefulRun

module EXP (A : Adversary) (pk : PubKey) (sk : SecKey)
           (rₐ : Rₐ)
           (v : PhaseNumber → Vec Rgb #q) (cs : CipherText ²)
           (ms : MarkedReceipt? ²) where
  BBsetup : BB
  BBsetup = []

  Aphase1 : Phase _
  Aphase1 = A rₐ pk

  S = BB × Fin #q

  -- When the adversary runs out of allowed queries (namely
  -- when i becomes zero), then all successive queries will
  -- be deterministic. The only case asking for randomness
  -- is ballot creation.
  OracleS : (phase# : 𝟚) (q : Q) → State S (Resp q)
  OracleS phase# q (bb , i) = O.resp q , O.newBB q , Fin.pred i
    where module O = Oracle sk pk (lookup i (v phase#)) bb

  phase1 = runS (OracleS 0₂) Aphase1 (BBsetup , max#q)

  AdversaryRFChallenge : RFChallenge _
  AdversaryRFChallenge = proj₁ phase1

  AdversarySN : SerialNumber ²
  AdversarySN = get-chal AdversaryRFChallenge

  BBphase1 : BB
  BBphase1 = proj₁ (proj₂ phase1)

  receipts : Receipt ²
  receipts c = ms c , AdversarySN c , cs c

  BBrfc : BB
  BBrfc = receipts ∷² BBphase1

  Aphase2 : Phase _
  Aphase2 = put-resp AdversaryRFChallenge receipts

  phase2 = runS (OracleS 1₂) Aphase2 (BBrfc , max#q)

  -- adversary guess
  b′ = proj₁ phase2

module SimpleScheme where
    R : ★
    R = Rₖ × Rₐ × 𝟚 × (Rₑ)² × (Vec Rgb #q)²

    ct-resp : (b : 𝟚) → PubKey → Rₑ ² → CipherText ²
    ct-resp b pk rₑ = Enc pk ∘ flip _xor_ b ˢ rₑ

    game : Adversary → R → 𝟚
    game A (rₖ , rₐ , b , rₑ , rgbs) =
      case KeyGen rₖ of λ
      { (pk , sk) →
        b == EXP.b′ A pk sk rₐ rgbs (ct-resp b pk rₑ) (const (marked 0₂))
      }

module LessSimpleScheme where
    R : ★
    R = Rₖ × Rₐ × 𝟚 × Rgb ² × (Vec Rgb #q)²

    module Receipts (b : 𝟚) (pk : PubKey) (rgb : Rgb ²) where

      ballots : Ballot ²
      ballots c = fillBallot c (genBallot pk (rgb c))

      ballot-for-alice = ballots alice
      ballot-for-bob   = ballots bob

      randomly-swapped-ballots : Ballot ²
      randomly-swapped-ballots = ballots ∘ _xor_ b

      randomly-swapped-receipts : Receipt ²
      randomly-swapped-receipts = receipt ∘ randomly-swapped-ballots

    game : Adversary → R → 𝟚
    game A (rₖ , rₐ , b , rgb , rgbs) =
      case KeyGen rₖ of λ
      { (pk , sk) →
        let
            open Receipts b pk rgb
            r = randomly-swapped-receipts
            ms = markedReceipt? ∘ r
            cs = enc-co ∘ r
        in
        b == EXP.b′ A pk sk rₐ rgbs cs ms
      }

    -- Winning condition
    Win : Adversary → R → ★
    Win A r = game A r ≡ 1₂
