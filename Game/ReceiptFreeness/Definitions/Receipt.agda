
{-# OPTIONS --without-K #-}
open import Function
open import Type
open import Data.Product renaming (zip to zip-×)
open import Data.Two
open import Data.List as L
open import Data.Nat.NP hiding (_==_)

module Game.ReceiptFreeness.Definitions.Receipt
  (CipherText : ★)

  (SerialNumber : ★)
  where

Candidate : ★
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

data CO-spec : CO → Candidate → Candidate → ★ where
  alice-then-bob-spec : CO-spec alice-then-bob alice bob
  bob-then-alice-spec : CO-spec bob-then-alice bob alice

MarkedReceipt : ★
MarkedReceipt = 𝟚

marked-on-first-cell marked-on-second-cell : MarkedReceipt
marked-on-first-cell  = 0₂
marked-on-second-cell = 1₂

data MarkedReceipt-spec : CO → MarkedReceipt → Candidate → ★ where
  m1 : MarkedReceipt-spec alice-then-bob marked-on-first-cell  alice
  m2 : MarkedReceipt-spec alice-then-bob marked-on-second-cell bob
  m3 : MarkedReceipt-spec bob-then-alice marked-on-first-cell  bob
  m4 : MarkedReceipt-spec bob-then-alice marked-on-second-cell alice

data MarkedReceipt? : ★ where
  not-marked : MarkedReceipt?
  marked     : MarkedReceipt → MarkedReceipt?

-- Receipt or also called RHS
-- Made of a potential mark, a serial number, and an encrypted candidate order
Receipt : ★
Receipt = MarkedReceipt? × SerialNumber × CipherText

markedReceipt? : Receipt → MarkedReceipt?
markedReceipt? = proj₁

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
enc-co = proj₂ ∘ proj₂

m? : Receipt → MarkedReceipt?
m? = proj₁

r-sn : Receipt → SerialNumber
r-sn = proj₁ ∘ proj₂

Ballot : ★
Ballot = CO × Receipt

b-sn : Ballot → SerialNumber
b-sn = r-sn ∘ proj₂

-- co or also called LHS
co : Ballot → CO
co = proj₁

-- receipt or also called RHS
receipt : Ballot → Receipt
receipt = proj₂

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

ClearReceipt : ★
ClearReceipt = CO × MarkedReceipt?

ClearBB : ★
ClearBB = List ClearReceipt
