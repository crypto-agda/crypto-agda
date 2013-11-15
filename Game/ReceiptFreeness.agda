-- {-# OPTIONS --without-K #-}
open import Function
open import Type
open import Data.Maybe.NP
open import Data.Fin.NP as Fin hiding (_+_; _==_)
open import Data.Product renaming (zip to zip-×)
open import Data.One
open import Data.Two
open import Data.Vec
open import Data.List as L

open import Data.Nat.NP renaming (_==_ to _==ℕ_)

open import Relation.Binary.PropositionalEquality
open import Control.Strategy

module Game.ReceiptFreeness
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
  (Check : CipherText → 𝟚)
  (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)

where

unchecked = 0₂
checked = 1₂

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

_² : ★ → ★
A ² = 𝟚 → A

-- How to read types as protocols:
-- A × B   sends A, then behave as B
-- A → B   receives A, then behave as B

RFChallenge : ★ → ★
RFChallenge Next = (SerialNumber ²) × (Receipt ² → Next)

Adversary : ★
Adversary = Rₐ → PubKey → Phase -- Phase[I]
                           (RFChallenge
                             (Phase -- Phase[II]
                               𝟚)) -- Adversary guess of whether the vote is for alice

-- TODO adversary validity
-- Valid-Adversary : Adversary → ★

module Oracle (sk : SecKey) (pk : PubKey) (rgb : Rgb) (bb : BB) where
    resp : (q : Q) → Resp q
    resp REB = genBallot pk rgb
    resp RBB = bb
    resp RTally = tally sk bb
    resp (RCO (_ , _ , receipt)) = Dec sk receipt
    -- do we check if the sn is already here?
    resp (Vote (m? , sn , receipt)) = [0: reject 1: accept ]′ (Check receipt)

    newBB : Q → BB
    newBB (Vote v) = [0: bb 1: v ∷ bb ]′ (Check (enc-co v))
    newBB _ = bb

private
  State : (S A : ★) → ★
  State S A = S → A × S
open StatefulRun

module ToBeUsedLater
   (b : 𝟚) (pk : PubKey)
   (rgb : Candidate → Rgb) {-
   (rco : Candidate → CO)
   (rₑ : Candidate → Rₑ)
   (sn : Candidate → SerialNumber)-} where

   {-
  rgb : Candidate → Rgb
  rgb c = rco c , sn c , rₑ c
  -}

  ballots : Candidate → Ballot
  ballots c = fillBallot c (genBallot pk (rgb c))

  ballot-for-alice = ballots alice
  ballot-for-bob   = ballots bob

  randomly-swapped-ballots : Candidate → Ballot
  randomly-swapped-ballots = ballots ∘ _xor_ b

  randomly-swapped-receipts : Candidate → Receipt
  randomly-swapped-receipts = receipt ∘ randomly-swapped-ballots

PhaseNumber = 𝟚
module EXP (b : 𝟚) (A : Adversary) (pk : PubKey) (sk : SecKey)
           (rₐ : Rₐ)
           (v : PhaseNumber → Vec Rgb #q) (cs : Candidate → CipherText)
           (ms : Candidate → MarkedReceipt?) where
  BBsetup : BB
  BBsetup = []

  Aphase[I] : Phase _
  Aphase[I] = A rₐ pk

  S = BB × Fin #q

  -- When the adversary runs out of allowed queries (namely
  -- when i becomes zero), then all successive queries will
  -- be deterministic. The only case asking for randomness
  -- is ballot creation.
  OracleS : (phase# : 𝟚) (q : Q) → State S (Resp q)
  OracleS phase# q (bb , i) = O.resp q , O.newBB q , Fin.pred i
    where module O = Oracle sk pk (lookup i (v phase#)) bb

  phase[I] = runS (OracleS 0₂) Aphase[I] (BBsetup , max#q)

  AdversaryRFChallenge : RFChallenge _
  AdversaryRFChallenge = proj₁ phase[I]

  AdversarySN : SerialNumber ²
  AdversarySN = proj₁ AdversaryRFChallenge

  BBphase[I] : BB
  BBphase[I] = proj₁ (proj₂ phase[I])

  receipts : Candidate → Receipt
  receipts c = ms c , AdversarySN c , cs c

  BBrfc : BB
  BBrfc = receipts 0₂ ∷ receipts 1₂ ∷ BBphase[I]

  Aphase[II] : Phase _
  Aphase[II] = proj₂ AdversaryRFChallenge receipts

  phase[II] = runS (OracleS 1₂) Aphase[II] (BBrfc , max#q)

  -- adversary guess
  b′ = proj₁ phase[II]

module SimpleScheme where
    R : ★
    R = Rₖ × Rₐ × 𝟚 × (Rₑ)² × (Vec Rgb #q)²

    game : Adversary → R → 𝟚
    game A (rₖ , rₐ , b , rₑ , rgbs) =
      case KeyGen rₖ of λ
      { (pk , sk) →
        b == EXP.b′ b A pk sk rₐ rgbs (Enc pk ˢ rₑ) (const (marked 0₂))
      }

module LessSimpleScheme where
    R : ★
    R = Rₖ × Rₐ × 𝟚 × Rgb ² × (Vec Rgb #q)²

    game : Adversary → R → 𝟚
    game A (rₖ , rₐ , b , rgb , rgbs) =
      case KeyGen rₖ of λ
      { (pk , sk) →
        let
            open ToBeUsedLater b pk rgb
            r = randomly-swapped-receipts
            ms = markedReceipt? ∘ r
            cs = enc-co ∘ r
        in
        b == EXP.b′ b A pk sk rₐ rgbs cs ms
      }

    -- Winning condition
    Win : Adversary → R → ★
    Win A r = game A r ≡ 1₂

{- Not all adversaries of the Adversary type are valid.

   First, we do not forbid the challenge in the 2nd step of the Oracle.
   Second, there is no check preventing ballots to be resubmitted.
   Last but not least, no complexity analysis is done.
-}

{-
module Cheating1 (sn : SerialNumber ²) where
    cheatingA : Adversary
    cheatingA rₐ pk = done (sn , λ m → ask (RCO (m 1₂)) (λ co → done (co == (marked-on-second-cell? (markedReceipt? (m 1₂))))))

    module _
     (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                           Dec sk (Enc pk m rₑ) ≡ m) where

        cheatingA-wins : ∀ r → game cheatingA r ≡ 1₂
        cheatingA-wins (rₖ , _ , 0₂ , co , rₑ , _)
          rewrite DecEnc rₖ (rₑ 1₂) (co 1₂) with co 1₂
        ... | 0₂ = refl
        ... | 1₂ = refl
        cheatingA-wins (rₖ , _ , 1₂ , co , rₑ , _)
          rewrite DecEnc rₖ (rₑ 0₂) (co 0₂) with co 0₂
        ... | 0₂ = refl
        ... | 1₂ = refl

module Cheating2 (sn : SerialNumber ²) where
    cheatingA : Adversary
    cheatingA rₐ pk = done (sn , λ m → ask (Vote (m 1₂))
                                     (λ { accept → ask RTally (λ { (x , y) →
                                     done (x ==ℕ 2) }) ; reject → done 1₂ }))

    module _
     (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                           Dec sk (Enc pk m rₑ) ≡ m) where

        cheatingA-wins : ∀ r → game cheatingA r ≡ 1₂
        cheatingA-wins (rₖ , _ , 0₂ , co , rₑ , _)
           rewrite CheckEnc (proj₁ (KeyGen rₖ)) (co 1₂) (rₑ 1₂)
                 | DecEnc rₖ (rₑ 0₂) (co 0₂)
                 | DecEnc rₖ (rₑ 1₂) (co 1₂) with co 0₂ | co 1₂
        ... | 0₂ | 0₂ = refl
        ... | 0₂ | 1₂ = refl
        ... | 1₂ | 0₂ = refl
        ... | 1₂ | 1₂ = refl
        cheatingA-wins (rₖ , _ , 1₂ , co , rₑ , _)
           rewrite CheckEnc (proj₁ (KeyGen rₖ)) (co 0₂) (rₑ 0₂)
                 | DecEnc rₖ (rₑ 0₂) (co 0₂)
                 | DecEnc rₖ (rₑ 1₂) (co 1₂) with co 0₂ | co 1₂
        ... | 0₂ | 0₂ = refl
        ... | 0₂ | 1₂ = refl
        ... | 1₂ | 0₂ = refl
        ... | 1₂ | 1₂ = refl
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
