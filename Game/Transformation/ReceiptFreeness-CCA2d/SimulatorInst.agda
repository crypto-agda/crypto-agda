{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.Two
open import Data.Product
open import Data.Nat
open import Data.Vec hiding (_>>=_ ; _∈_)
open import Data.List as L
open import Data.Fin as Fin using (Fin)
open import Control.Strategy renaming (map to mapS)
open import Control.Strategy.Utils
open import Game.Challenge
import Game.ReceiptFreeness
import Game.ReceiptFreeness.Adversary
import Game.IND-CCA2-dagger
import Game.IND-CPA-utils
import Game.Transformation.ReceiptFreeness-CCA2d.Simulator

import Data.List.Any
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

module Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst
  (PubKey    : ★)
  (SecKey    : ★)
  -- (Message   : ★)
  (CipherText : ★)

  (SerialNumber : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  (#q : ℕ) (max#q : Fin #q)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : let Message = 𝟚 in PubKey → Message → Rₑ → CipherText)
  (Dec    : let Message = 𝟚 in SecKey → CipherText → Message)
  (Check    : let open Game.ReceiptFreeness PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec
               in BB → Receipt → 𝟚)
  -- (CheckMem : ∀ bb r → ✓ (Check bb r) → proj₁ (proj₂ r) ∉ L.map (proj₁ ∘ proj₂) bb)
  -- (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)
  where

open Game.ReceiptFreeness PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec

module Receipts (m : 𝟚) (sn : SerialNumber ²) (ct : CipherText ²) where
  receipts : Receipt ²
  receipts c = marked m , sn c , ct c

open Game.Transformation.ReceiptFreeness-CCA2d.Simulator PubKey CipherText (SerialNumber ²) Receipt MarkedReceipt? Ballot Tally
       BB [] _∷_ Rgb genBallot tallyMarkedReceipt? (0 , 0) (1 , 1) _+,+_ (Receipts.receipts 0₂) enc-co m? Rₐ #q max#q Check public

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
