{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.Two
open import Data.Product
open import Data.Nat
open import Data.Maybe
open import Data.Vec hiding (_>>=_ ; _∈_)
open import Data.List as L
open import Data.Fin as Fin using (Fin)
open import Control.Strategy renaming (map to mapS)
open import Control.Strategy.Utils

open import Crypto.Schemes
open import Game.Challenge
import Game.ReceiptFreeness
import Game.ReceiptFreeness.Adversary
import Game.IND-CCA2-dagger
import Game.IND-CPA-utils
import Game.Transformation.ReceiptFreeness-CCA2d.Simulator

import Data.List.Any
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

module Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst
  (pke : Pubkey-encryption)
  (open Pubkey-encryption pke)
  (SerialNumber : Type)
  (Rₐ : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  (#q : ℕ) (max#q : Fin #q)
  (Check    : let open Game.ReceiptFreeness pke SerialNumber Rₐ 𝟚→Message Message→𝟚 #q max#q
               in BB → Receipt → 𝟚)
  -- (CheckMem : ∀ bb r → ✓ (Check bb r) → proj₁ (proj₂ r) ∉ L.map (proj₁ ∘ proj₂) bb)
  -- (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)
  where

open Game.ReceiptFreeness pke SerialNumber Rₐ 𝟚→Message Message→𝟚 #q max#q

module Receipts (m : 𝟚) (sn : SerialNumber ²) (ct : CipherText ²) where
  receipts : Receipt ²
  receipts c = marked m , sn c , ct c

open Game.Transformation.ReceiptFreeness-CCA2d.Simulator PubKey CipherText (SerialNumber ²) Receipt MarkedReceipt? Ballot Tally
       BB [] _∷_ Rgb genBallot tallyMarkedReceipt? (0 , 0) (1 , 1) _+,+_ (Receipts.receipts 0₂) enc-co m? Rₐ #q max#q Check
       Message 𝟚→Message Message→𝟚 public

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
