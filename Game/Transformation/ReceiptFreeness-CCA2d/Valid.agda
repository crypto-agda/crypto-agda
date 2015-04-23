{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Vec hiding (_>>=_ ; _∈_)
open import Data.List as L
open import Data.Fin as Fin using (Fin)
open import Relation.Binary.PropositionalEquality.NP as ≡
open import Control.Strategy renaming (map to mapS)
open import Control.Strategy.Utils
open import Game.Challenge
import Game.ReceiptFreeness
import Game.IND-CCA2-dagger
import Game.IND-CCA2-dagger.Valid
import Game.IND-CPA-utils

import Data.List.Any
open Data.List.Any using (here; there)
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

import Game.ReceiptFreeness.Adversary
import Game.ReceiptFreeness.Valid
import Game.Transformation.ReceiptFreeness-CCA2d.Simulator

module Game.Transformation.ReceiptFreeness-CCA2d.Valid
  (PubKey    : ★)
  (CipherText : ★)

  (SerialNumber : ★)
  (Receipt : ★)
  (MarkedReceipt? : ★)
  (Ballot : ★)
  (Tally : ★)
--  (BB    : ★)
--  ([]    : BB)
--  (_∷_ : Receipt → BB → BB)
  (Rgb   : ★)
  (genBallot : PubKey → Rgb → Ballot)
  (tallyMarkedReceipt? : let CO = 𝟚 in CO → MarkedReceipt? → Tally)
  (0,0   : Tally)
  (1,1   : Tally)
  (_+,+_ : Tally → Tally → Tally)
  (receipts : SerialNumber ² → CipherText ² → Receipt ²)
  (enc-co : Receipt → CipherText)
  (r-sn   : Receipt → SerialNumber)
  (m?     : Receipt → MarkedReceipt?)
  (b-sn   : Ballot → SerialNumber)
  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₐ : ★)
  (#q : ℕ) (max#q : Fin #q)
  (Check    : let BB = List Receipt in BB → Receipt → 𝟚)
  where

_²' : ★ → ★
X ²' = X × X

CO = 𝟚
BB = List Receipt
all-sn : BB → List SerialNumber
all-sn = L.map r-sn

module RF  = Game.ReceiptFreeness.Adversary PubKey (SerialNumber ²) Rₐ Receipt Ballot Tally CO BB
module RFV = Game.ReceiptFreeness.Valid     PubKey SerialNumber Rₐ Receipt Ballot Tally CO BB
                                            CipherText enc-co r-sn b-sn

open Game.Transformation.ReceiptFreeness-CCA2d.Simulator
  PubKey CipherText (SerialNumber ²) Receipt MarkedReceipt? Ballot Tally BB [] _∷_ Rgb genBallot
  tallyMarkedReceipt? 0,0 1,1 _+,+_ receipts enc-co m? Rₐ #q max#q Check

module CCA2†V = Game.IND-CCA2-dagger.Valid PubKey Message CipherText Rₐ†


module Simulator-Valid (RFA : RF.Adversary)(RFA-Valid : RFV.Valid-Adversary RFA)
  (WRONG-HYP : ∀ r r' → enc-co r ≡ enc-co r' → r-sn r ≡ r-sn r')
  (CheckMem : ∀ bb r → ✓ (Check bb r) → r-sn r ∉ all-sn bb)
  where
  valid : CCA2†V.Valid-Adversary (Simulator.A† RFA)
  valid (rₐ , rgb) pk = Phase1 _ (RFA-Valid rₐ pk) where
     open CCA2†V.Valid-Adversary (rₐ , rgb) pk
     module RFVA = RFV.Valid-Adversary rₐ pk
     open RF
     open Simulator RFA
     open AdversaryParts rgb pk rₐ

     -- could refine r more
     -- {-
     Phase2 : ∀ RF {bb i ta r} → r-sn (r 0₂) ∈ all-sn bb → r-sn (r 1₂) ∈ all-sn bb → RFVA.Phase2-Valid r RF
            → Phase2-Valid (enc-co ∘ r) (mapS proj₁ (mitm-to-client-trans (MITM-phase 1₂ i bb ta) RF))
     Phase2 (ask REB cont) r0 r1 RF-valid = Phase2 (cont _) r0 r1 (RF-valid _)
     Phase2 (ask RBB cont) r0 r1 RF-valid = Phase2 (cont _) r0 r1 (RF-valid _)
     Phase2 (ask RTally cont) r0 r1 RF-valid = Phase2 (cont _) r0 r1 (RF-valid _)
     Phase2 (ask (RCO x) cont) r0 r1 ((r₀ , r₁) , RF-valid) = r₀ , r₁ , (λ r → Phase2 (cont _) r0 r1 (RF-valid _))
     Phase2 (ask (Vote x) cont) {bb} r0 r1 RF-valid with Check bb x | CheckMem bb x
     ... | 0₂ | _ = Phase2 (cont _) r0 r1 (RF-valid _)
     ... | 1₂ | not-in-bb = (λ eq → not-in-bb _ (tr (λ x₁ → x₁ ∈ all-sn bb) (WRONG-HYP _ _  eq) r0))
                            , (λ eq → not-in-bb _ (tr (λ x₁ → x₁ ∈ all-sn bb) (WRONG-HYP _ _ eq) r1))
                            , λ r → Phase2 (cont _) (there r0) (there r1) (RF-valid _)
                            --Phase2 (cont _) (there r0) (there r1) (RF-valid _)
     Phase2 (done x) r0 r1 RF-valid = RF-valid

     Phase1 : ∀ RF {sn i bb ta} → RFVA.Phase1-Valid sn RF
            → Phase1-Valid (mapS A†2 (mitm-to-client-trans (MITM-phase 0₂ i bb ta) RF))
     Phase1 (ask REB cont) RF-valid = Phase1 _ (RF-valid _)
     Phase1 (ask RBB cont) RF-valid = Phase1 _ (RF-valid _)
     Phase1 (ask RTally cont) RF-valid = Phase1 _ (RF-valid _)
     Phase1 (ask (RCO x) cont) RF-valid r = Phase1 _ (RF-valid _)
     Phase1 (ask (Vote x) cont) {bb = bb} RF-valid with Check bb x
     Phase1 (ask (Vote x) cont) RF-valid | 1₂ = λ r → Phase1 _ (RF-valid _)
     Phase1 (ask (Vote x) cont) RF-valid | 0₂ = Phase1 _ (RF-valid _)
     Phase1 (done x) {bb = bb'}{ta} (sn₀∉sn , sn₁∉sn , RF-valid) cs
       = {!Phase2 (put-resp x (proj₂ (put-resp (hack-challenge x) cs)))!}
       -- {!Phase2 (put-resp x (proj₂ (put-resp (hack-challenge x) cs))) (here refl) (there (here refl)) (RF-valid _)!}
       -- Phase2 (put-resp x (proj₂ (put-resp (hack-challenge x) cs) ))
       --     ? ? (RF-valid _)
    -- -}

-- -}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
