open import Function using (_∘_; flip; _ˢ_)
open import Type using (Type)
open import Data.Fin.NP using (Fin)
open import Data.List as L
open import Data.Maybe
open import Data.Nat.NP using (ℕ)
open import Data.Product using (_×_ ; proj₁ ; proj₂; _,_)
open import Data.Two using (𝟚 ; ✓; _²; 0₂; 1₂; _xor_)
import Data.List.Any
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

open import Crypto.Schemes
import Relation.Binary.PropositionalEquality.NP as ≡

-- module that re-exports the important definitions for the ReceiptFreeness game
module Game.ReceiptFreeness
  (pke : Pubkey-encryption)
  (open Pubkey-encryption pke)
  (SerialNumber : Type)
  (Rₐ : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  (#q : ℕ) (max#q : Fin #q)
  where

-- open import Game.ReceiptFreeness.Definitions pke SerialNumber Rₐ 𝟚→Message Message→𝟚 public
open import Game.ReceiptFreeness.ValidInst   pke SerialNumber Rₐ 𝟚→Message Message→𝟚 public

EncReceipts : PubKey → Rₑ ² → SerialNumber ² → CO → Receipt ²
EncReceipts pk rₑ sn b i = marked 0₂ , sn i , enc pk (𝟚→Message (i xor b)) (rₑ i)

DecReceipt' : SecKey → Receipt → CO
DecReceipt' sk r = proj₁ (DecReceipt sk r)

import Game.ReceiptFreeness.Experiment

{- Agda bug?
module Experiment = Game.ReceiptFreeness.Experiment
    PubKey SecKey (SerialNumber ²) (Rₑ ²) Rₖ Rₐ #q max#q key-gen
    Receipt EncReceipts DecReceipt' Rgb Ballot BB [] _∷_ genBallot Tally tally
-}

module Experiment Check =
  Game.ReceiptFreeness.Experiment
    PubKey SecKey (SerialNumber ²) (Rₑ ²) Rₖ Rₐ #q max#q key-gen
    Receipt EncReceipts DecReceipt' Rgb Ballot BB [] _∷_ genBallot Tally tally
    Check

-- -}
-- -}
-- -}
-- -}
-- -}
