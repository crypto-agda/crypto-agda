{-# OPTIONS --without-K #-}
open import Function
open import Type
open import Data.Product renaming (zip to zip-×)
open import Data.Two
open import Data.List as L
open import Data.Nat.NP hiding (_==_)
import Game.ReceiptFreeness.Definitions.Encryption
import Game.ReceiptFreeness.Definitions.Receipt
import Game.ReceiptFreeness.Definitions.Tally

module Game.ReceiptFreeness.Definitions
  (PubKey    : ★)
  (SecKey    : ★)
  -- Message = 𝟚
  (CipherText : ★)

  (SerialNumber : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₐ : ★)
  (Enc    : let Message = 𝟚 in
            PubKey → Message → Rₑ → CipherText)
  (Dec    : let Message = 𝟚 in
            SecKey → CipherText → Message)
  where

open Game.ReceiptFreeness.Definitions.Receipt CipherText SerialNumber public
open Game.ReceiptFreeness.Definitions.Tally CipherText SerialNumber public
open Game.ReceiptFreeness.Definitions.Encryption PubKey SecKey CipherText SerialNumber Rₑ Enc Dec public
open import Game.ReceiptFreeness.Adversary PubKey (SerialNumber ²) Rₐ Receipt Ballot Tally CO BB public

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
