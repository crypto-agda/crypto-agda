{-# OPTIONS --without-K --copatterns #-}
open import Function
open import Type
open import Data.Fin as Fin
open import Data.Nat.NP using (ℕ)
open import Data.One
open import Data.Product
open import Data.Two
import Data.List as L
open L using (List; _∷_ ; [])
open import Data.Vec

open import Game.Challenge
open import Control.Protocol.CoreOld
open import Control.Strategy

open import Relation.Binary.PropositionalEquality.NP as ≡
import Game.ReceiptFreeness.Protocol

module Game.ReceiptFreeness.ProtocolImplementation
  (PubKey    : Type)
  (SecKey    : Type)

  (SerialNumber² : Type)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ² Rₖ : Type)
  (#q : ℕ) (max#q : Fin #q)
  (key-gen : Rₖ → PubKey × SecKey)
  (Receipt : Type)

  -- CO is the message
  -- Receipt ² is the ciphertext
  (enc-receipts : let CO = 𝟚 in PubKey → Rₑ² → SerialNumber² → CO → Receipt ²)
  (dec-receipt  : let CO = 𝟚 in SecKey → Receipt → CO)

  (Rgb : Type)
  (Ballot : Type)
  (BB : Type)
  ([] : BB)
  (_∷_ : Receipt → BB → BB)
  (gen-ballot : PubKey → Rgb → Ballot)
  (Tally : Type)
  (tally : SecKey → BB → Tally)
  (check : BB → Receipt → 𝟚)
  where

_∷²_ : Receipt ² → BB → BB
p ∷² xs = p 0₂ ∷ (p 1₂ ∷ xs)

CO = 𝟚
PhaseNumber = 𝟚

open Game.ReceiptFreeness.Protocol PubKey SerialNumber² Receipt Ballot BB Tally CO
open Explicit-definitions

module Oracle (sk : SecKey) (pk : PubKey) (rgb : Rgb) (bb : BB) where
  resp : (q : Q) → Resp q
  resp REB = gen-ballot pk rgb
  resp RBB = bb
  resp RTally = tally sk bb
  resp (RCO receipt) = dec-receipt sk receipt
  -- do we check if the sn is already here?
  resp (Vote v) = [0: reject 1: accept ]′ (check bb v)

module Chal (b : 𝟚)(pk : PubKey)(sk : SecKey)(v : PhaseNumber → Vec Rgb #q)(rₑ : Rₑ²) where

  newBB : BB → Q → BB
  newBB bb (Vote v) = [0: bb 1: v ∷ bb ]′ (check bb v)
  newBB bb _ = bb

  module _ X p# (cont : BB → El 𝟙 X) where
    service : BB → Fin #q → El 𝟙 (Round X)
    srv-ask (service bb i) q = Oracle.resp sk pk (lookup i (v p#)) bb q , service (newBB bb q) (pred i)
    srv-done (service bb _) = cont bb

  phase2 : BB → Fin #q → El 𝟙 (Round end)
  phase2 = service end 1₂ (λ _ → _)

  exc : BB → El 𝟙 (Exchange (Round end))
  exc bb sn = r² , (phase2 (r² ∷² bb) max#q)
    where r² = enc-receipts pk rₑ sn b

  phase1 : BB → Fin #q → El 𝟙 (Round (Exchange (Round end)))
  phase1 = service (Exchange (Round end)) 0₂ exc

RF-C : (b : 𝟚)(rₖ : Rₖ)(v : PhaseNumber → Vec Rgb #q)(rₑ : Rₑ²) → El 𝟙 ReceiptFreeness
RF-C b rₖ v rₑ =
  let pk , sk = key-gen rₖ
      BBsetup = []
  in pk , Chal.phase1 b pk sk v rₑ BBsetup max#q


-- -}
-- -}
-- -}
-- -}
-- -}
