{-# OPTIONS --without-K #-}

open import Function
open import Type
open import Data.Maybe
open import Data.Fin hiding (_+_)
open import Data.Product renaming (zip to zip-×)
--open import Data.One
open import Data.Two
open import Data.List as L

open import Data.Nat.NP hiding (_==_)

{-
open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open Operators
open import Relation.Binary.PropositionalEquality
-}
--open import Control.Strategy renaming (run to runStrategy)


module Game.ReceiptFreeness
  (PubKey    : ★)
  (SecKey    : ★)
  -- Message = 𝟚
  (CipherText : ★)
  (CheckedCipherText : ★)

  (SerialNumber : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : let Message = 𝟚 in
            PubKey → Message → Rₑ → CheckedCipherText)
  (forget : CheckedCipherText → CipherText)
  (check  : CipherText → Maybe CheckedCipherText)
  (Dec    : let Message = 𝟚 in
            SecKey → CheckedCipherText → Message)

where

data Strategy (Q : ★) (R : Q → ★) (A : ★) : ★ where
  ask  : (q? : Q) (cont : R q? → Strategy Q R A) → Strategy Q R A
  done : A → Strategy Q R A

module _ {Q : ★} {R : Q → ★} (Oracle : (q : Q) → R q) where
  private
    M = Strategy Q R
  run : ∀ {A} → M A → A
  run (ask q? cont) = run (cont (Oracle q?))
  run (done x)      = x

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
alice-then-bob = 0₂
bob-then-alice = 1₂

data CO-spec : CO → Candidate → Candidate → ★ where
  01₂ : CO-spec 0₂ 0₂ 1₂
  10₂ : CO-spec 1₂ 1₂ 0₂

alice-then-bob-spec : CO-spec alice-then-bob alice bob
alice-then-bob-spec = 01₂

bob-then-alice-spec : CO-spec bob-then-alice bob alice
bob-then-alice-spec = 10₂

MarkedRHS : ★
MarkedRHS = 𝟚

data MarkedRHS-spec : MarkedRHS → ★ where
  marked-on-first-cell  : MarkedRHS-spec 0₂
  marked-on-second-cell : MarkedRHS-spec 1₂

Receipt : ★
Receipt = SerialNumber × CipherText

CheckedReceipt : ★
CheckedReceipt = SerialNumber × CheckedCipherText
  
data MarkedRHS? : ★ where
  not-marked : MarkedRHS?
  marked     : MarkedRHS → MarkedRHS?
  
RHS : ★
RHS = Receipt × MarkedRHS?

CheckedRHS : ★
CheckedRHS = CheckedReceipt × MarkedRHS?

receipt : RHS → Receipt
receipt = proj₁

markedRHS? : RHS → MarkedRHS?
markedRHS? = proj₂

-- Marked when there is a 1
marked? : MarkedRHS? → 𝟚
marked? not-marked = 0₂
marked? (marked x) = 1₂

first-mark : MarkedRHS? → 𝟚
first-mark not-marked = 0₂
first-mark (marked x) = x == 0₂

second-mark : MarkedRHS? → 𝟚
second-mark not-marked = 0₂
second-mark (marked x) = x == 1₂

Ballot : ★
Ballot = CO × RHS

CheckedBallot : ★
CheckedBallot = CO × RHS

Rgb : ★
Rgb = CO × Rₑ

genBallot : Rgb → SerialNumber → PubKey → Ballot
genBallot (rCO , rₑ) sn pk = rCO , ((sn , forget (Enc pk rCO rₑ)) , not-marked)

lhs : Ballot → CO
lhs = proj₁

rhs : Ballot → RHS
rhs = proj₂

BB : ★
BB = List CheckedRHS

Tally : ★
Tally = ℕ × ℕ

data Accept? : ★ where
  accept reject : Accept?

-- In the paper RBB is the returning the Tally and we
-- return the BB, here RTally is returning the Tally
data Q : ★ where
  REB RBB RTally : Q
  RCO            : CheckedRHS → Q
  Vote           : RHS → Q

Resp : Q → ★
Resp REB = Ballot
Resp (RCO x) = CO
Resp (Vote x) = Accept?
Resp RBB = BB
Resp RTally = Tally

Phase : ★ → ★
Phase = Strategy Q Resp

-- A × B   sends A, then behave as B
-- A → B   receives A, then behave as B

RFChallenge : ★ → ★
RFChallenge Next = (𝟚 → Receipt) → Next

Adversary : ★
Adversary = Rₐ → PubKey → Phase -- Phase[I]
                           (RFChallenge
                             (Phase -- Phase[II]
                               𝟚)) -- Adversary guess of whether the vote is for alice

-- TODO adversary validity

tallyMarkedRHS : CO → MarkedRHS → Tally
tallyMarkedRHS co m = 𝟚▹ℕ for-alice , 𝟚▹ℕ (not for-alice)
  where for-alice = co == m

1:alice-0:bob 0:alice-1:bob : Tally
1:alice-0:bob = 1 , 0
0:alice-1:bob = 0 , 1

data TallyMarkedRHS-spec : CO → MarkedRHS → Tally → ★ where
  -- CO is alice-then-bob
  c1 : TallyMarkedRHS-spec alice-then-bob{-0-} 0₂ 1:alice-0:bob
  c2 : TallyMarkedRHS-spec alice-then-bob{-0-} 1₂ 0:alice-1:bob

  -- CO is bob-then-alice
  c3 : TallyMarkedRHS-spec bob-then-alice{-1-} 0₂ 0:alice-1:bob
  c4 : TallyMarkedRHS-spec bob-then-alice{-1-} 1₂ 1:alice-0:bob

tallyMarkedRHS-ok : ∀ co m → TallyMarkedRHS-spec co m (tallyMarkedRHS co m)
tallyMarkedRHS-ok 1₂ 1₂ = c4
tallyMarkedRHS-ok 1₂ 0₂ = c3
tallyMarkedRHS-ok 0₂ 1₂ = c2
tallyMarkedRHS-ok 0₂ 0₂ = c1

tallyCheckedRHS : SecKey → CheckedRHS → Tally
tallyCheckedRHS sk (r , not-marked) = 0 , 0
tallyCheckedRHS sk ((sn , co) , marked x) = tallyMarkedRHS (Dec sk co) x

tally : SecKey → BB → Tally
tally sk bb = L.foldr (zip-× _+_ _+_) (0 , 0) (L.map (tallyCheckedRHS sk) bb)

R : ★
R = Rₖ × Rₐ × (Fin {!!} → Rgb) × {!!}

-- Return
Game : ★
Game = Adversary → R → 𝟚

module _ (sk : SecKey) (pk : PubKey) (rgb : Rgb) (sn : SerialNumber) (bb : BB) where
    Oracle : (q : Q) → Resp q
    Oracle REB = genBallot rgb sn pk
    Oracle RBB = bb
    Oracle RTally = tally sk bb
    Oracle (RCO ((sn , receipt) , m?)) = Dec sk receipt

    -- do we check if the sn is already here?
    Oracle (Vote ((sn , receipt) , m?)) = case check receipt of λ { (just x) → accept ; nothing → reject }

    OracleBB : Q → BB
    OracleBB REB = bb
    OracleBB RBB = bb
    OracleBB RTally = bb
    OracleBB (RCO _) = bb

    -- do we check if the sn is already here?
    OracleBB (Vote ((sn , receipt) , m?)) = case check receipt of λ { (just x) → ((sn , x) , m?) ∷ bb ; nothing → bb }

⅁ : Game
⅁ A (rₖ , rₐ , rgbs , _) =
  -- setup
  case KeyGen rₖ of λ
  { (pk , sk) →
    let bb = [] in
    let Asetup = A rₐ pk in
    let Aphase[I] = run (Oracle sk pk (rgbs {!!}) {!!} {!bb!}) Asetup in
    {!!}
  }
-- -}
-- -}
-- -}
-- -}
