{-# OPTIONS --without-K #-}
open import Function
open import Type
open import Data.Product.NP renaming (zip to zip-×)
open import Data.Two
open import Data.List as L
open import Data.Nat.NP hiding (_==_)

module Game.ReceiptFreeness.Definitions.Receipt
  (CipherText : Type)
  (SerialNumber : Type)
  where

Candidate : Type
Candidate = 𝟚 -- as in the paper: "for simplicity"

alice bob : Candidate
alice = 0₂
bob   = 1₂

-- candidate order
-- also known as LHS or Message
-- represented by who is the first candidate
CO = 𝟚

alice-then-bob bob-then-alice : CO
alice-then-bob = alice
bob-then-alice = bob

data CO-spec : CO → Candidate → Candidate → Type where
  alice-then-bob-spec : CO-spec alice-then-bob alice bob
  bob-then-alice-spec : CO-spec bob-then-alice bob alice

MarkedReceipt : Type
MarkedReceipt = 𝟚

marked-on-first-cell marked-on-second-cell : MarkedReceipt
marked-on-first-cell  = 0₂
marked-on-second-cell = 1₂

data MarkedReceipt-spec : CO → MarkedReceipt → Candidate → Type where
  m1 : MarkedReceipt-spec alice-then-bob marked-on-first-cell  alice
  m2 : MarkedReceipt-spec alice-then-bob marked-on-second-cell bob
  m3 : MarkedReceipt-spec bob-then-alice marked-on-first-cell  bob
  m4 : MarkedReceipt-spec bob-then-alice marked-on-second-cell alice

data MarkedReceipt? : Type where
  not-marked : MarkedReceipt?
  marked     : MarkedReceipt → MarkedReceipt?

-- Receipt or also called RHS
-- Made of a potential mark, a serial number, and an encrypted candidate order
Receipt : Type
Receipt = MarkedReceipt? × SerialNumber × CipherText

markedReceipt? : Receipt → MarkedReceipt?
markedReceipt? = fst

-- Marked when there is a 1
marked? : MarkedReceipt? → 𝟚
marked? not-marked = 0₂
marked? (marked _) = 1₂

marked-on-first-cell? : MarkedReceipt? → 𝟚
marked-on-first-cell? not-marked = 0₂
marked-on-first-cell? (marked x) = x == 0₂

marked-on-second-cell? : MarkedReceipt? → 𝟚
marked-on-second-cell? not-marked = 0₂
marked-on-second-cell? (marked x) = x == 1₂

enc-co : Receipt → CipherText
enc-co = snd ∘ snd

m? : Receipt → MarkedReceipt?
m? = fst

r-sn : Receipt → SerialNumber
r-sn = fst ∘ snd

Ballot : Type
Ballot = CO × Receipt

b-sn : Ballot → SerialNumber
b-sn = r-sn ∘ snd

-- co or also called LHS
co : Ballot → CO
co = fst

-- receipt or also called RHS
receipt : Ballot → Receipt
receipt = snd

mark : CO → Candidate → MarkedReceipt
mark co c = co xor c

mark-ok : ∀ co c → MarkedReceipt-spec co (mark co c) c
mark-ok 1₂ 1₂ = m3
mark-ok 1₂ 0₂ = m4
mark-ok 0₂ 1₂ = m2
mark-ok 0₂ 0₂ = m1

fillBallot : Candidate → Ballot → Ballot
fillBallot c (co , _ , sn , enc-co) = co , marked (mark co c) , sn , enc-co

-- TODO Ballot-spec c (fillBallot b)

ClearReceipt : Type
ClearReceipt = CO × MarkedReceipt?

ClearBB : Type
ClearBB = List ClearReceipt
