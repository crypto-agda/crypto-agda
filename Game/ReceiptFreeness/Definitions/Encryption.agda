{-# OPTIONS --without-K #-}
open import Function
open import Type
open import Data.Product renaming (zip to zip-×)
open import Data.Two
open import Data.List as L
open import Data.Nat.NP hiding (_==_)
import Game.ReceiptFreeness.Definitions.Receipt
import Game.ReceiptFreeness.Definitions.Tally

module Game.ReceiptFreeness.Definitions.Encryption
  (PubKey    : ★)
  (SecKey    : ★)
  -- Message = 𝟚
  (CipherText : ★)

  (SerialNumber : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ : ★)
  (Enc    : let Message = 𝟚 in
            PubKey → Message → Rₑ → CipherText)
  (Dec    : let Message = 𝟚 in
            SecKey → CipherText → Message)
  where

open Game.ReceiptFreeness.Definitions.Receipt CipherText SerialNumber
open Game.ReceiptFreeness.Definitions.Tally CipherText SerialNumber


-- randomness for genBallot
Rgb : ★
Rgb = CO × SerialNumber × Rₑ

genBallot : PubKey → Rgb → Ballot
genBallot pk (r-co , sn , rₑ) = r-co , not-marked , sn , Enc pk r-co rₑ


BB : ★
BB = List Receipt

DecReceipt : SecKey → Receipt → CO × MarkedReceipt?
DecReceipt sk (m? , sn , enc-co) = Dec sk enc-co , m?

DecBB : SecKey → BB → ClearBB
DecBB = L.map ∘ DecReceipt

-- Not taking advantage of any homomorphic encryption
tally : SecKey → BB → Tally
tally sk bb = tallyClearBB (DecBB sk bb)
