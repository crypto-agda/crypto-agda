open import Type
open import Data.Fin.NP using (Fin)
open import Data.Nat.NP using (ℕ)
open import Data.One using (𝟙)
open import Data.List as L
open import Data.Product
open import Data.Two
open import Game.Challenge
open import Control.Strategy
open import Relation.Binary.PropositionalEquality

import Data.List.Any
open Data.List.Any.Membership-≡ using (_∉_)


import Game.ReceiptFreeness.Definitions
import Game.ReceiptFreeness.Valid

module Game.ReceiptFreeness.ValidInst
  (PubKey SecKey CipherText SerialNumber Rₑ Rₐ : ★)
  (Enc    : let Message = 𝟚 in
            PubKey → Message → Rₑ → CipherText)
  (Dec    : let Message = 𝟚 in
            SecKey → CipherText → Message)
  where

open Game.ReceiptFreeness.Definitions PubKey SecKey CipherText SerialNumber Rₑ Rₐ Enc Dec
open Game.ReceiptFreeness.Valid PubKey SerialNumber Rₐ Receipt Ballot Tally CO BB CipherText enc-co r-sn b-sn public
