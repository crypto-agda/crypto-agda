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
  (CipherText : (checked? : 𝟚) → ★)

  (SerialNumber : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  (#q : ℕ) (max#q : Fin #q)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : let Message = 𝟚 in
            PubKey → Message → Rₑ → CipherText 1₂)
  (forget : CipherText 1₂ → CipherText 0₂)
  (check  : CipherText 0₂ → Maybe (CipherText 1₂))
  (Dec    : let Message = 𝟚 in
            SecKey → CipherText 1₂ → Message)

where

Checked? = 𝟚
checked unchecked : Checked?
unchecked = 0₂
checked = 1₂


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
Receipt : (checked? : 𝟚) → ★
Receipt checked? = MarkedReceipt? × SerialNumber × CipherText checked?

forgetReceipt : Receipt checked → Receipt unchecked
forgetReceipt (m? , sn , enc-co) = m? , sn , forget enc-co

checkReceipt : Receipt unchecked → Maybe (Receipt checked)
checkReceipt (m? , sn , ck-enc-co) = map? (λ x → m? , sn , x) (check ck-enc-co)

markedReceipt? : ∀ {checked?} → Receipt checked? → MarkedReceipt?
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

Ballot : (checked? : 𝟚) → ★
Ballot checked? = CO × Receipt checked?

-- co or also called LHS
co : ∀ {checked?} → Ballot checked? → CO
co = proj₁

-- receipt or also called RHS
receipt : ∀ {checked?} → Ballot checked? → Receipt checked?
receipt = proj₂

-- randomness for genBallot
Rgb : ★
Rgb = CO × SerialNumber × Rₑ

genBallot : PubKey → Rgb → Ballot checked
genBallot pk (r-co , sn , rₑ) = r-co , not-marked , sn , Enc pk r-co rₑ

forgetBallot : Ballot checked → Ballot unchecked
forgetBallot (co , m? , sn , enc-co) = co , m? , sn , forget enc-co

mark : CO → Candidate → MarkedReceipt
mark co c = co xor c

mark-ok : ∀ co c → MarkedReceipt-spec co (mark co c) c
mark-ok 1₂ 1₂ = m3
mark-ok 1₂ 0₂ = m4
mark-ok 0₂ 1₂ = m2
mark-ok 0₂ 0₂ = m1

fillBallot : ∀ {checked?} → Candidate → Ballot checked? → Ballot checked?
fillBallot c (co , _ , sn , enc-co) = co , marked (mark co c) , sn , enc-co

-- TODO Ballot-spec c (fillBallot b)

BB : ★
BB = List (Receipt checked)

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

tallyCheckedReceipt : SecKey → Receipt checked → Tally
tallyCheckedReceipt sk (marked? , _ , enc-co) = tallyMarkedReceipt? (Dec sk enc-co) marked?

-- Not taking advantage of any homomorphic encryption
tally : SecKey → BB → Tally
tally sk bb = L.foldr (zip-× _+_ _+_) (0 , 0) (L.map (tallyCheckedReceipt sk) bb)

data Accept? : ★ where
  accept reject : Accept?

-- In the paper RBB is the returning the Tally and we
-- return the BB, here RTally is returning the Tally
data Q : ★ where
  REB RBB RTally : Q
  RCO            : Receipt checked → Q
  Vote           : Receipt unchecked → Q

Resp : Q → ★
Resp REB = Ballot unchecked
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
RFChallenge Next = (𝟚 → Receipt checked) → Next

Adversary : ★
Adversary = Rₐ → PubKey → Phase -- Phase[I]
                           (RFChallenge
                             (Phase -- Phase[II]
                               𝟚)) -- Adversary guess of whether the vote is for alice

-- TODO adversary validity
-- Valid-Adversary : Adversary → ★

module Oracle (sk : SecKey) (pk : PubKey) (rgb : Rgb) (bb : BB) where
    resp : (q : Q) → Resp q
    resp REB = forgetBallot (genBallot pk rgb)
    resp RBB = bb
    resp RTally = tally sk bb
    resp (RCO (_ , _ , receipt)) = Dec sk receipt
    -- do we check if the sn is already here?
    resp (Vote (m? , sn , receipt)) = case check receipt of λ { (just x) → accept ; nothing → reject }

    newBB : Q → BB
    newBB (Vote (m? , sn , receipt)) = case check receipt of λ { (just x) → (m? , sn , x) ∷ bb ; nothing → bb }
    newBB _ = bb

PhaseNumber = 𝟚
module EXP (b : 𝟚) (A : Adversary) (pk : PubKey) (sk : SecKey)
           (rₐ : Rₐ) (rgb : Candidate → Rgb)
           (v : PhaseNumber → Vec Rgb #q) where
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

  BBphase[I] : BB
  BBphase[I] = proj₁ (proj₂ phase[I])

  ballots : Candidate → Ballot checked
  ballots c = fillBallot c (genBallot pk (rgb c))

  ballot-for-alice = ballots alice
  ballot-for-bob   = ballots bob

  randomly-swapped-ballots : Candidate → Ballot checked
  randomly-swapped-ballots = ballots ∘ _xor_ b

  randomly-swapped-receipts : Candidate → Receipt checked
  randomly-swapped-receipts = receipt ∘ randomly-swapped-ballots

  BBrfc : BB
  BBrfc = randomly-swapped-receipts 0₂ ∷ randomly-swapped-receipts 1₂ ∷ BBphase[I]

  Aphase[II] : Phase _
  Aphase[II] = AdversaryRFChallenge randomly-swapped-receipts

  phase[II] = runS (OracleS 1₂) Aphase[II] (BBrfc , max#q)

  -- adversary guess
  b′ = proj₁ phase[II]

_² : ★ → ★
A ² = A × A

R : ★
R = Rₖ × Rₐ × 𝟚 × (Vec Rgb (1{-for the challenge-} + #q))²

game : Adversary → R → 𝟚
game A (rₖ , rₐ , b , (rgb₀ ∷ rgbs₀) , (rgb₁ ∷ rgbs₁)) =
  case KeyGen rₖ of λ
  { (pk , sk) →
    b == EXP.b′ b A pk sk rₐ [0: rgb₀ 1: rgb₁ ] [0: rgbs₀ 1: rgbs₁ ]
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
    cheatingA rₐ pk = done (λ m → ask (RCO (m 1₂)) (λ co → done (co == (marked-on-second-cell? (markedReceipt? (m 1₂))))))

    module _
     (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                           Dec sk (Enc pk m rₑ) ≡ m) where

        cheatingA-wins : ∀ r → game cheatingA r ≡ 1₂
        cheatingA-wins (rₖ , _ , 0₂ , ((co₀ , _ , rₑ₀) ∷ _) , ((co₁ , _ , rₑ₁) ∷ _))
          rewrite DecEnc rₖ rₑ₁ co₁ with co₁
        ... | 0₂ = refl
        ... | 1₂ = refl
        cheatingA-wins (rₖ , _ , 1₂ , ((co₀ , _ , rₑ₀) ∷ _) , ((_ , _ , rₑ₁) ∷ _))
          rewrite DecEnc rₖ rₑ₀ co₀ with co₀
        ... | 0₂ = refl
        ... | 1₂ = refl

module Cheating2 where
    cheatingA : Adversary
    cheatingA rₐ pk = done λ m → ask (Vote (forgetReceipt (m 1₂)))
                                     (λ { accept → ask RTally (λ { (x , y) →
                                     done (x ==ℕ 2) }) ; reject → done 1₂ })

    module _
     (DecEnc : ∀ rₖ rₑ m → let (pk , sk) = KeyGen rₖ in
                           Dec sk (Enc pk m rₑ) ≡ m)
     (check-forget : ∀ x → check (forget x) ≡ just x)
                       where

        cheatingA-wins : ∀ r → game cheatingA r ≡ 1₂
        cheatingA-wins (rₖ , _ , 0₂ , ((co₀ , _ , rₑ₀) ∷ _) , ((co₁ , _ , rₑ₁) ∷ _))
           rewrite check-forget (Enc (proj₁ (KeyGen rₖ)) co₁ rₑ₁)
                 | DecEnc rₖ rₑ₀ co₀
                 | DecEnc rₖ rₑ₁ co₁ with co₀ | co₁
        ... | 0₂ | 0₂ = refl
        ... | 0₂ | 1₂ = refl
        ... | 1₂ | 0₂ = refl
        ... | 1₂ | 1₂ = refl
        cheatingA-wins (rₖ , _ , 1₂ , ((co₀ , _ , rₑ₀) ∷ _) , ((co₁ , _ , rₑ₁) ∷ _)) -- = {!!}
           rewrite check-forget (Enc (proj₁ (KeyGen rₖ)) co₀ rₑ₀)
                 | DecEnc rₖ rₑ₀ co₀
                 | DecEnc rₖ rₑ₁ co₁ with co₀ | co₁
        ... | 0₂ | 0₂ = refl
        ... | 0₂ | 1₂ = refl
        ... | 1₂ | 0₂ = refl
        ... | 1₂ | 1₂ = refl
-- -}
-- -}
-- -}
-- -}
