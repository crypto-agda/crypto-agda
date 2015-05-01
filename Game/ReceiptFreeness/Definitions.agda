{-# OPTIONS --without-K #-}
open import Function
open import Type
open import Data.Product renaming (zip to zip-×)
open import Data.Two
open import Data.Maybe
open import Data.List as L
open import Data.Nat.NP hiding (_==_)
open import Crypto.Schemes
import Game.ReceiptFreeness.Definitions.Encryption
import Game.ReceiptFreeness.Definitions.Receipt
import Game.ReceiptFreeness.Definitions.Tally

module Game.ReceiptFreeness.Definitions
  (pke : Pubkey-encryption)
  (open Pubkey-encryption pke)
  (SerialNumber : Type)
  (Rₐ : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  where

open Game.ReceiptFreeness.Definitions.Receipt CipherText SerialNumber public
open Game.ReceiptFreeness.Definitions.Tally CipherText SerialNumber public
open Game.ReceiptFreeness.Definitions.Encryption pke SerialNumber 𝟚→Message Message→𝟚 public
open import Game.ReceiptFreeness.Adversary PubKey (SerialNumber ²) Rₐ Receipt Ballot Tally CO BB public

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
