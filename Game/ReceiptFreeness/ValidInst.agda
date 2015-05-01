{-# OPTIONS --without-K #-}
open import Type
open import Data.Two
open import Data.Maybe

open import Crypto.Schemes
import Game.ReceiptFreeness.Definitions
import Game.ReceiptFreeness.Valid

module Game.ReceiptFreeness.ValidInst
  (pke : Pubkey-encryption)
  (open Pubkey-encryption pke)
  (SerialNumber : Type)
  (Rₐ : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  where

open Game.ReceiptFreeness.Definitions pke SerialNumber Rₐ 𝟚→Message Message→𝟚 public
open Game.ReceiptFreeness.Valid PubKey SerialNumber Rₐ Receipt Ballot Tally CO BB CipherText enc-co r-sn b-sn public
