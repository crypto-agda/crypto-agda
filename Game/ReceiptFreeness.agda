open import Function using (_∘_; flip; _ˢ_)
open import Type using (★)
open import Data.Fin.NP using (Fin)
open import Data.List as L
open import Data.Nat.NP using (ℕ)
open import Data.Product using (_×_ ; proj₁ ; proj₂; _,_)
open import Data.Two using (𝟚 ; ✓; _²; 0₂; 1₂; _xor_)
import Data.List.Any
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

import Relation.Binary.PropositionalEquality.NP as ≡

-- module that re-exports the important definitions for the ReceiptFreeness game
module Game.ReceiptFreeness
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

  where

open import Game.ReceiptFreeness.Definitions PubKey SecKey CipherText SerialNumber Rₑ Rₐ Enc Dec public
open import Game.ReceiptFreeness.Valid       PubKey SecKey CipherText SerialNumber Rₑ Rₐ Enc Dec public

EncReceipts : PubKey → Rₑ ² → SerialNumber ² → CO → Receipt ²
EncReceipts pk rₑ sn b i = marked 0₂ , sn i , Enc pk (i xor b) (rₑ i)

DecReceipt' : SecKey → Receipt → CO
DecReceipt' sk r = proj₁ (DecReceipt sk r)

import Game.ReceiptFreeness.Experiment

{- Agda bug?
module Experiment = Game.ReceiptFreeness.Experiment
    PubKey SecKey (SerialNumber ²) (Rₑ ²) Rₖ Rₐ #q max#q KeyGen
    Receipt EncReceipts DecReceipt' Rgb Ballot BB [] _∷_ genBallot Tally tally
-}

module Experiment Check where
  open Game.ReceiptFreeness.Experiment
    PubKey SecKey (SerialNumber ²) (Rₑ ²) Rₖ Rₐ #q max#q KeyGen
    Receipt EncReceipts DecReceipt' Rgb Ballot BB [] _∷_ genBallot Tally tally
    Check public

-- -}
-- -}
-- -}
-- -}
-- -}
