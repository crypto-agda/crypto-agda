-- {-# OPTIONS --without-K #-}


open import Function
open import Type
open import Data.Maybe
open import Data.Fin.NP as Fin hiding (_+_; _==_)
open import Data.Product renaming (zip to zip-×)
open import Data.One
open import Data.Two
open import Data.Vec
open import Data.List as L

open import Data.Nat.NP renaming (_==_ to _==ℕ_)

{-
open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open Operators
-}
open import Relation.Binary.PropositionalEquality
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
  (#q : ℕ) (max#q : Fin #q)
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

State : (S A : ★) → ★
State S A = S → A × S

module _ {S Q : ★} {R : Q → ★} (Oracle : (q : Q) → State S (R q)) where
  private
    M = Strategy Q R
  runS : ∀ {A} → M A → State S A
  runS (ask q? cont) s = case Oracle q? s of λ { (x , s') → runS (cont x) s' }
  runS (done x)      s = x , s

  evalS : ∀ {A} → M A → S → A
  evalS x s = proj₁ (runS x s)

  execS : ∀ {A} → M A → S → S
  execS x s = proj₂ (runS x s)

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
  alice-then-bob-spec : CO-spec alice-then-bob alice bob
  bob-then-alice-spec : CO-spec bob-then-alice bob alice

MarkedRHS : ★
MarkedRHS = 𝟚

marked-on-first-cell marked-on-second-cell : MarkedRHS
marked-on-first-cell  = 0₂
marked-on-second-cell = 1₂

data MarkedRHS-spec : MarkedRHS → ★ where
  marked-on-first-cell-spec  : MarkedRHS-spec marked-on-first-cell
  marked-on-second-cell-spec : MarkedRHS-spec marked-on-second-cell

-- CipherText is the encrypted candidate order
Receipt : ★
Receipt = SerialNumber × CipherText

CheckedReceipt : ★
CheckedReceipt = SerialNumber × CheckedCipherText

forgetReceipt : CheckedReceipt → Receipt
forgetReceipt (sn , encCO) = sn , forget encCO

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
marked? (marked _) = 1₂

marked-on-first-cell? : MarkedRHS? → 𝟚
marked-on-first-cell? not-marked = 0₂
marked-on-first-cell? (marked x) = x == 0₂

marked-on-second-cell? : MarkedRHS? → 𝟚
marked-on-second-cell? not-marked = 0₂
marked-on-second-cell? (marked x) = x == 1₂

Ballot : ★
Ballot = CO × RHS

-- unused
CheckedBallot : ★
CheckedBallot = CO × CheckedRHS

-- randomness for genBallot
Rgb : ★
Rgb = CO × SerialNumber × Rₑ

genBallot : PubKey → Rgb → Ballot
genBallot pk (rCO , sn , rₑ) = rCO , (sn , forget (Enc pk rCO rₑ)) , not-marked

lhs : Ballot → CO
lhs = proj₁

rhs : Ballot → RHS
rhs = proj₂

BB : ★
BB = List CheckedRHS

Tally : ★
Tally = ℕ × ℕ

alice-score : Tally → ℕ
alice-score = proj₁

bob-score : Tally → ℕ
bob-score = proj₂

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

-- How to read types as protocols:
-- A × B   sends A, then behave as B
-- A → B   receives A, then behave as B

RFChallenge : ★ → ★
RFChallenge Next = (𝟚 → CheckedReceipt) → Next

Adversary : ★
Adversary = Rₐ → PubKey → Phase -- Phase[I]
                           (RFChallenge
                             (Phase -- Phase[II]
                               𝟚)) -- Adversary guess of whether the vote is for alice

-- TODO adversary validity

1:alice-0:bob 0:alice-1:bob : Tally
1:alice-0:bob = 1 , 0
0:alice-1:bob = 0 , 1

data TallyMarkedRHS-spec : CO → MarkedRHS → Tally → ★ where
  c1 : TallyMarkedRHS-spec alice-then-bob marked-on-first-cell  1:alice-0:bob
  c2 : TallyMarkedRHS-spec alice-then-bob marked-on-second-cell 0:alice-1:bob
  c3 : TallyMarkedRHS-spec bob-then-alice marked-on-first-cell  0:alice-1:bob
  c4 : TallyMarkedRHS-spec bob-then-alice marked-on-second-cell 1:alice-0:bob

tallyMarkedRHS : CO → MarkedRHS → Tally
tallyMarkedRHS co m = 𝟚▹ℕ for-alice , 𝟚▹ℕ (not for-alice)
  where for-alice = co == m

tallyMarkedRHS-ok : ∀ co m → TallyMarkedRHS-spec co m (tallyMarkedRHS co m)
tallyMarkedRHS-ok 1₂ 1₂ = c4
tallyMarkedRHS-ok 1₂ 0₂ = c3
tallyMarkedRHS-ok 0₂ 1₂ = c2
tallyMarkedRHS-ok 0₂ 0₂ = c1

tallyCheckedRHS : SecKey → CheckedRHS → Tally
tallyCheckedRHS sk (_ , not-marked) = 0 , 0
tallyCheckedRHS sk ((_ , encCO) , marked mark) = tallyMarkedRHS (Dec sk encCO) mark

-- Not taking advantage of any homomorphic encryption
tally : SecKey → BB → Tally
tally sk bb = L.foldr (zip-× _+_ _+_) (0 , 0) (L.map (tallyCheckedRHS sk) bb)

module _ (sk : SecKey) (pk : PubKey) (rgb : Rgb) (bb : BB) where
    Oracle : (q : Q) → Resp q
    Oracle REB = genBallot pk rgb
    Oracle RBB = bb
    Oracle RTally = tally sk bb
    Oracle (RCO ((_ , receipt) , _)) = Dec sk receipt
    -- do we check if the sn is already here?
    Oracle (Vote ((sn , receipt) , m?)) = case check receipt of λ { (just x) → accept ; nothing → reject }

    OracleBB : Q → BB
    OracleBB REB = bb
    OracleBB RBB = bb
    OracleBB RTally = bb
    OracleBB (RCO _) = bb
    OracleBB (Vote ((sn , receipt) , m?)) = case check receipt of λ { (just x) → ((sn , x) , m?) ∷ bb ; nothing → bb }

module EXP (b : 𝟚) (A : Adversary) (pk : PubKey) (sk : SecKey)
           (rₐ : Rₐ) (crₑ : 𝟚 → Rₑ) (csn : 𝟚 → SerialNumber)
           (v : 𝟚 → Vec Rgb #q) where
  BBsetup : BB
  BBsetup = []

  Aphase[I] : Phase _
  Aphase[I] = A rₐ pk

  S = BB × Fin #q

  OracleS : (phase# : 𝟚) (q : Q) → State S (Resp q)
  OracleS phase# q (bb , i) = Oracle sk pk rgb bb q , OracleBB sk pk rgb bb q , Fin.pred i
    where rgb = lookup i (v phase#)

  phase[I] = runS (OracleS 0₂) Aphase[I] (BBsetup , max#q)

  ARFChallenge : RFChallenge _
  ARFChallenge = proj₁ phase[I]

  BBphase[I] : BB
  BBphase[I] = proj₁ (proj₂ phase[I])

  Aphase[II] : Phase _
  Aphase[II] = ARFChallenge (λ i → csn i , Enc pk (i == b) (crₑ i))

  phase[II] = runS (OracleS 1₂) Aphase[II] (BBphase[I] , max#q)

  -- adversary guess
  b′ = proj₁ phase[II]

_² : ★ → ★
A ² = A × A

R : ★
R = Rₖ × Rₐ × 𝟚 × (Rₑ × SerialNumber × Vec Rgb #q)²

game : Adversary → R → 𝟚
game A (rₖ , rₐ , b , (rₑ₀ , sn₀ , rgbs₀) , (rₑ₁ , sn₁ , rgbs₁)) =
  case KeyGen rₖ of λ
  { (pk , sk) →
    b == EXP.b′ b A pk sk rₐ [0: rₑ₀ 1: rₑ₁ ] [0: sn₀ 1: sn₁ ] [0: rgbs₀ 1: rgbs₁ ]
  }

-- Winning condition
Win : Adversary → R → ★
Win A r = game A r ≡ 1₂

{- Not all adversaries of the Adversary type are valid.

   First, we do not forbid the challenge in the 2nd step of the Oracle.
   Second, no complexity analysis is done.
-}

module Cheating1 where
    cheatingA : Adversary
    cheatingA rₐ pk = done (λ m → ask (RCO (m 1₂ , marked 1₂)) done)

    module _
     (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                           Dec sk (Enc pk m rₑ) ≡ m) where

        cheatingA-wins : ∀ r → game cheatingA r ≡ 1₂
        cheatingA-wins (rₖ , _ , b , (rₑ₀ , _) , (rₑ₁ , _))
          rewrite DecEnc rₖ rₑ₀ b | DecEnc rₖ rₑ₁ b = ✓→≡ (==-refl {b})

module Cheating2 where
    cheatingA : Adversary
    cheatingA rₐ pk = done λ m → ask (Vote (forgetReceipt (m 1₂) , marked 1₂))
                                     (λ { accept → ask RTally (λ { (x , y) →
                                     done (x ==ℕ 1) }) ; reject → done 1₂ })

    module _
     (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                           Dec sk (Enc pk m rₑ) ≡ m)
     (check-forget : ∀ x → check (forget x) ≡ just x)
                       where

        cheatingA-wins : ∀ r → game cheatingA r ≡ 1₂
        cheatingA-wins (rₖ , rₐ , b , (rₑ₀ , proj₂) , rₑ₁ , proj₃)
           rewrite check-forget (Enc (proj₁ (KeyGen rₖ)) b rₑ₁)
                 | DecEnc rₖ rₑ₁ b with b
        ... | 0₂ = {!!}
        ... | 1₂ = {!!}
                 {-
        cheatingA-wins (rₖ , rₐ , 1₂ , (rₑ₀ , proj₂) , rₑ₁ , proj₃)
           rewrite check-forget (Enc (proj₁ (KeyGen rₖ)) 1₂ rₑ₁)
                 | DecEnc rₖ rₑ₁ 1₂ = refl
        cheatingA-wins (rₖ , rₐ , 0₂ , (rₑ₀ , proj₂) , rₑ₁ , proj₃)
           rewrite check-forget (Enc (proj₁ (KeyGen rₖ)) 0₂ rₑ₁)
                 | DecEnc rₖ rₑ₁ 0₂ = refl
-- -}
-- -}
-- -}
-- -}
