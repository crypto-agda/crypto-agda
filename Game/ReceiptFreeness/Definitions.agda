--{-# OPTIONS --without-K #-}
{-# OPTIONS --copatterns #-}
open import Function
open import Type
open import Data.Maybe.NP
open import Data.Fin.NP as Fin hiding (_+_; _==_)
open import Data.Product renaming (zip to zip-×)
open import Data.One
open import Data.Two
open import Data.Vec
open import Data.List as L
import Data.List.Any as LA
import Data.Vec.NP

open import Data.Nat.NP renaming (_==_ to _==ℕ_)

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as ≡
open import Control.Strategy
open import Game.Challenge
open module MM {X : ★} = LA.Membership (≡.setoid X) using (_∈_ ; _∉_)

module Game.ReceiptFreeness.Definitions
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
 -- (Check : CipherText → 𝟚)
 -- (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)

  where

_∷²_ : ∀ {a} {A : ★_ a} → A ² → List A → List A
p ∷² xs = p 0₂ ∷ p 1₂ ∷ xs

{-
_∷²_ : ∀ {a} {A : ★_ a} {n} → A ² → Vec A n → Vec A (2 + n)
p ∷² xs = p 0₂ ∷ p 1₂ ∷ xs
-}

Candidate : ★
Candidate = 𝟚 -- as in the paper: "for simplicity"

alice bob : Candidate
alice = 0₂
bob   = 1₂

-- candidate order
-- also known as LHS or Message
-- represented by who is the first candidate
CO : ★
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

Ballot : ★
Ballot = CO × Receipt

-- co or also called LHS
co : Ballot → CO
co = proj₁

-- receipt or also called RHS
receipt : Ballot → Receipt
receipt = proj₂

-- randomness for genBallot
Rgb : ★
Rgb = CO × SerialNumber × Rₑ

genBallot : PubKey → Rgb → Ballot
genBallot pk (r-co , sn , rₑ) = r-co , not-marked , sn , Enc pk r-co rₑ

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

BB : ★
BB = List Receipt

ClearReceipt : ★
ClearReceipt = CO × MarkedReceipt?

ClearBB : ★
ClearBB = List ClearReceipt

Tally : ★
Tally = ℕ × ℕ

alice-score : Tally → ℕ
alice-score = proj₁

bob-score : Tally → ℕ
bob-score = proj₂

1:alice-0:bob 0:alice-1:bob : Tally
1:alice-0:bob = 1 , 0
0:alice-1:bob = 0 , 1

data TallyMarkedReceipt-spec : CO → MarkedReceipt → Tally → ★ where
  c1 : TallyMarkedReceipt-spec alice-then-bob marked-on-first-cell  1:alice-0:bob
  c2 : TallyMarkedReceipt-spec alice-then-bob marked-on-second-cell 0:alice-1:bob
  c3 : TallyMarkedReceipt-spec bob-then-alice marked-on-first-cell  0:alice-1:bob
  c4 : TallyMarkedReceipt-spec bob-then-alice marked-on-second-cell 1:alice-0:bob

marked-for-alice? : CO → MarkedReceipt → 𝟚
marked-for-alice? co m = co == m

marked-for-bob? : CO → MarkedReceipt → 𝟚
marked-for-bob? co m = not (marked-for-alice? co m)

tallyMarkedReceipt : CO → MarkedReceipt → Tally
tallyMarkedReceipt co m = 𝟚▹ℕ for-alice , 𝟚▹ℕ (not for-alice)
  where for-alice = marked-for-alice? co m

tallyMarkedReceipt-ok : ∀ co m → TallyMarkedReceipt-spec co m (tallyMarkedReceipt co m)
tallyMarkedReceipt-ok 1₂ 1₂ = c4
tallyMarkedReceipt-ok 1₂ 0₂ = c3
tallyMarkedReceipt-ok 0₂ 1₂ = c2
tallyMarkedReceipt-ok 0₂ 0₂ = c1

tallyMarkedReceipt? : CO → MarkedReceipt? → Tally
tallyMarkedReceipt? co not-marked    = 0 , 0
tallyMarkedReceipt? co (marked mark) = tallyMarkedReceipt co mark

_+,+_ : Tally → Tally → Tally
_+,+_ = zip-× _+_ _+_

-- Not taking advantage of any homomorphic encryption
tallyClearBB : ClearBB → Tally
tallyClearBB = L.foldr _+,+_ (0 , 0) ∘ L.map (uncurry tallyMarkedReceipt?)

DecReceipt : SecKey → Receipt → CO × MarkedReceipt?
DecReceipt sk (m? , sn , enc-co) = Dec sk enc-co , m?

DecBB : SecKey → BB → ClearBB
DecBB = L.map ∘ DecReceipt

-- Not taking advantage of any homomorphic encryption
tally : SecKey → BB → Tally
tally sk bb = tallyClearBB (DecBB sk bb)

data Accept? : ★ where
  accept reject : Accept?

-- In the paper RBB is the returning the Tally and we
-- return the BB, here RTally is returning the Tally
data Q : ★ where
  REB RBB RTally : Q
  RCO            : Receipt → Q
  Vote           : Receipt → Q

Resp : Q → ★
Resp REB = Ballot
Resp (RCO x) = CO
Resp (Vote x) = Accept?
Resp RBB = BB
Resp RTally = Tally

Phase : ★ → ★
Phase = Strategy Q Resp

-- How to read types as protocols:
-- A × B   sends A, then behave as B
-- A → B   receives A, then behave as B

RFChallenge : ★ → ★
RFChallenge = ChalAdversary (SerialNumber ²) (Receipt ²)

Adversary : ★
Adversary = Rₐ → PubKey → Phase -- Phase1
                           (RFChallenge -- give two serial numbers, get back two receipts
                             (Phase -- Phase2
                               𝟚)) -- Adversary guess of whether the vote is for alice

PhaseNumber : ★
PhaseNumber = 𝟚


  

{-
  -- {-
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
