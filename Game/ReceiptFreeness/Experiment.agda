open import Function
open import Type
open import Data.Fin as Fin
open import Data.Nat.NP using (ℕ)
open import Data.Two
open import Data.Product
import Data.List as L
open L using (List; _∷_ ; [])
open import Data.Vec

open import Game.Challenge
open import Control.Strategy

open import Relation.Binary.PropositionalEquality.NP as ≡
import Game.ReceiptFreeness.Adversary

module Game.ReceiptFreeness.Experiment
  (PubKey    : ★)
  (SecKey    : ★)

  (SerialNumber² : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ² Rₖ Rₐ : ★)
  (#q : ℕ) (max#q : Fin #q)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Receipt : ★)

  -- CO is the message
  -- Receipt ² is the ciphertext
  (EncReceipts : let CO = 𝟚 in
                 PubKey → Rₑ² → SerialNumber² → CO → Receipt ²)

  (DecReceipt : let CO = 𝟚 in
                SecKey → Receipt → CO)

  (Rgb : ★)
  (Ballot : ★)
  (BB : ★)
  ([] : BB)
  (_∷_ : Receipt → BB → BB)
  (genBallot : PubKey → Rgb → Ballot)
  (Tally : ★)
  (tally : SecKey → BB → Tally)
  (Check : BB → Receipt → 𝟚)
  where

_∷²_ : Receipt ² → BB → BB
p ∷² xs = p 0₂ ∷ (p 1₂ ∷ xs)

CO = 𝟚

open Game.ReceiptFreeness.Adversary PubKey SerialNumber² Rₐ Receipt Ballot Tally CO BB

private
  State : (S A : ★) → ★
  State S A = S → A × S
open StatefulRun

module Oracle (sk : SecKey) (pk : PubKey) (rgb : Rgb) (bb : BB) where
  resp : (q : Q) → Resp q
  resp REB = genBallot pk rgb
  resp RBB = bb
  resp RTally = tally sk bb
  resp (RCO receipt) = DecReceipt sk receipt
  -- do we check if the sn is already here?
  resp (Vote v) = [0: reject 1: accept ]′ (Check bb v)

  newBB : Q → BB
  newBB (Vote v) = [0: bb 1: v ∷ bb ]′ (Check bb v)
  newBB _ = bb

module OracleS (sk : SecKey) (pk : PubKey) (v : PhaseNumber → Vec Rgb #q) where
  S = BB × Fin #q

  -- When the adversary runs out of allowed queries (namely
  -- when i becomes zero), then all successive queries will
  -- be deterministic. The only case asking for randomness
  -- is ballot creation.
  OracleS : (phase# : 𝟚) (q : Q) → State S (Resp q)
  OracleS phase# q (bb , i) = resp q , newBB q , Fin.pred i
    where open Oracle sk pk (lookup i (v phase#)) bb

module EXP (b : 𝟚) (A : Adversary) (pk : PubKey) (sk : SecKey)
           (rₐ : Rₐ)
           (v : PhaseNumber → Vec Rgb #q)
           (rₑ : Rₑ²) where
  open OracleS sk pk v

  BBsetup : BB
  BBsetup = []

  Aphase1 : Phase _
  Aphase1 = A rₐ pk

  phase1,state = runS (OracleS 0₂) Aphase1 (BBsetup , max#q)

  AdversaryRFChallenge : RFChallenge _
  AdversaryRFChallenge = proj₁ phase1,state

  AdversarySN : SerialNumber²
  AdversarySN = get-chal AdversaryRFChallenge

  BBphase1 : BB
  BBphase1 = proj₁ (proj₂ phase1,state)

  receipts : Receipt ²
  receipts = EncReceipts pk rₑ AdversarySN b

  BBrfc : BB
  BBrfc = receipts ∷² BBphase1

  Aphase2 : Phase _
  Aphase2 = put-resp AdversaryRFChallenge receipts

  phase2 = runS (OracleS 1₂) Aphase2 (BBrfc , max#q)

  -- adversary guess
  b′ = proj₁ phase2

R : ★
R = Rₖ × Rₐ × 𝟚 × Rₑ² × (Vec Rgb #q)²

game : Adversary → R → 𝟚
game A (rₖ , rₐ , b , rₑ , rgbs) =
  case KeyGen rₖ of λ
  { (pk , sk) →
    b == EXP.b′ b A pk sk rₐ rgbs rₑ
  }

-- Winning condition
Win : Adversary → R → ★
Win A r = game A r ≡ 1₂

        {-

      ballots : Ballot ²
      ballots c = fillBallot c (genBallot pk (rgb c))

      ballot-for-alice = ballots alice
      ballot-for-bob   = ballots bob

      randomly-swapped-ballots : Ballot ²
      randomly-swapped-ballots = ballots ∘ _xor_ b

      randomly-swapped-receipts : Receipt ²
      randomly-swapped-receipts = receipt ∘ randomly-swapped-ballots

-- -}
-- -}
-- -}
-- -}
-- -}
