{-# OPTIONS --without-K #-}
open import Function
open import Type
open import Data.Product renaming (zip to zip-×)
open import Data.Two
open import Data.Maybe.NP
open import Data.List as L
open import Data.Nat.NP hiding (_==_)
open import Relation.Binary.PropositionalEquality.NP

open import Crypto.Schemes
import Game.ReceiptFreeness.Definitions.Receipt
import Game.ReceiptFreeness.Definitions.Tally

module Game.ReceiptFreeness.Definitions.Encryption
  (pke : Pubkey-encryption)
  (open Pubkey-encryption pke)
  (SerialNumber : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  where

open Game.ReceiptFreeness.Definitions.Receipt CipherText SerialNumber
open Game.ReceiptFreeness.Definitions.Tally   CipherText SerialNumber

-- randomness for genBallot
Rgb : Type
Rgb = CO × SerialNumber × Rₑ

genBallot : PubKey → Rgb → Ballot
genBallot pk (r-co , sn , rₑ) = r-co , not-marked , sn , enc pk (𝟚→Message r-co) rₑ

BB : Type
BB = List Receipt

DecReceipt : SecKey → Receipt → CO × MarkedReceipt?
DecReceipt sk (m? , sn , enc-co) = Message→𝟚 (dec sk enc-co) , m?

DecBB : SecKey → BB → ClearBB
DecBB = L.map ∘ DecReceipt

-- Not taking advantage of any homomorphic encryption
tally : SecKey → BB → Tally
tally sk bb = tallyClearBB (DecBB sk bb)
