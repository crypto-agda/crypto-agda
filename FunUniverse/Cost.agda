-- NOTE with-K
module FunUniverse.Cost where

open import Data.Nat.NP using (ℕ; zero; suc; _+_; _*_; 2*_; 2^_; _^_; _⊔_; module ℕ°; module ⊔°; 2*′_)
open import Data.Bool using (true; false)
open import Data.One
import Data.DifferenceNat
import Data.Vec.NP as V
import Function as F
import Data.Product as ×
import Relation.Binary.PropositionalEquality as ≡
open F using (const; _∘′_)
open V using (Vec; []; _∷_; _++_; [_])
open × using (_×_)
open ≡ using (_≡_; _≗_)
open import Level.NP hiding (_⊔_)

open import Data.Bits using (Bits; 0∷_; 1∷_; _→ᵇ_)

open import FunUniverse.Core
open import FunUniverse.Category
open import FunUniverse.Rewiring.Linear
open import FunUniverse.Const

module D where
  open Data.DifferenceNat public renaming (suc to suc#; _+_ to _+#_)
  _*#_ : ℕ → Diffℕ → Diffℕ
  zero  *# d = 0#
  suc n *# d = (n *# d) +# d
  _*#′_ : ℕ → Diffℕ → Diffℕ
  zero  *#′ d = 0#
  suc n *#′ d = d +# (n *#′ d)
  2*#_ : Diffℕ → Diffℕ
  2*# n = n +# n
  2^#_ : ℕ → Diffℕ
  2^# zero = 1#
  2^# suc n = 2*# (2^# n)
  1+_+_D : Diffℕ → Diffℕ → Diffℕ
  1+ x + y D = 1# ∘′ (x ∘′ y)
open D using (Diffℕ)

private
  1+_+_ : ℕ → ℕ → ℕ
  1+ x + y = 1 + (x + y)
  1+_⊔_ : ℕ → ℕ → ℕ
  1+ x ⊔ y = 1 + (x ⊔ y)
  i⊔i≡i : ∀ i → i ⊔ i ≡ i
  i⊔i≡i zero = ≡.refl
  i⊔i≡i (suc i) = ≡.cong suc (i⊔i≡i i)

{-
seqTimeOpsD : FunOps (constFuns Diffℕ)
seqTimeOpsD = record {
            id = 0#; _∘_ = _∘′_;
            <0b> = 0#; <1b> = 0#; cond = 1#; fork = 1+_+_D; tt = 0#;
            <_,_> = _∘′_; fst = 0#; snd = 0#;
            dup = 0#; first = F.id; swap = 0#; assoc = 0#;
            <tt,id> = 0#; snd<tt,> = 0#;
            <_×_> = _∘′_; second = F.id;
            <[]> = 0#; <∷> = 0#; uncons = 0# }
            where open D

module SeqTimeOpsD where
  Time = Diffℕ
  open D
  open FunOps seqTimeOpsD public

  snoc≡0 : ∀ n → snoc {n} ≗ 0#
  snoc≡0 zero x = ≡.refl
  snoc≡0 (suc n) x rewrite snoc≡0 n x = ≡.refl

  reverse≡0 : ∀ n → reverse {n} ≗ 0#
  reverse≡0 zero x = ≡.refl
  reverse≡0 (suc n) x rewrite reverse≡0 n x | snoc≡0 n x = ≡.refl

  replicate≡0 : ∀ n → replicate {n} ≗ 0#
  replicate≡0 zero = λ _ → ≡.refl
  replicate≡0 (suc n) = replicate≡0 n

  constBit≡0 : ∀ b → constBit b ≗ 0#
  constBit≡0 true  {-1b-} _ = ≡.refl
  constBit≡0 false {-0b-} _ = ≡.refl

  sum′ : ∀ {n} → Vec Diffℕ n → Diffℕ
  sum′ = V.foldr (const Diffℕ) _∘′_ id

  constVec≡sum : ∀ {n b} {B : Set b} (f : B → Time) xs → constVec {n} f xs ≗ sum′ (V.map f xs)
  constVec≡sum f [] x = ≡.refl
  constVec≡sum {suc n} f (b ∷ bs) x rewrite ℕ°.+-comm (f b x ⊔ constVec f bs x) 0
                                          | constVec≡sum f bs x = ≡.refl

  constBits≡0 : ∀ {n} xs → constBits {n} xs ≗ 0#
  constBits≡0 [] x = ≡.refl
  constBits≡0 {suc n} (b ∷ bs) x rewrite constBits≡0 bs x
                                       | constBit≡0 b x = ≡.refl

  foldl≡* : ∀ m n → foldl {m} n ≗ m *# n
  foldl≡* zero    n x = ≡.refl
  foldl≡* (suc m) n x rewrite foldl≡* m n (n x) = ≡.refl

  foldr≡* : ∀ m n → foldr {m} n ≗ m *#′ n
  foldr≡* zero    n x = ≡.refl
  foldr≡* (suc m) n x rewrite foldr≡* m n x = ≡.refl

  #nodes : ∀ i → Diffℕ
  #nodes zero    = 0#
  #nodes (suc i) = 1# +# #nodes i +# #nodes i

  fromBitsFun≡ : ∀ {i o} (f : i →ᵇ o) → fromBitsFun f ≗ #nodes i
  fromBitsFun≡ {zero} f x = constBits≡0 (f []) x
  fromBitsFun≡ {suc i} f x rewrite fromBitsFun≡ {i} (f ∘′ 1∷_) x
                                 | fromBitsFun≡ {i} (f ∘′ 0∷_) (#nodes i x) = ≡.refl
-}

Time = ℕ
TimeCost = constFuns Time
Space = ℕ
SpaceCost = constFuns Space

seqTimeCat : Category {₀} {₀} {𝟙} (λ _ _ → Time)
seqTimeCat = 0 , _+_

seqTimeLin : LinRewiring TimeCost
seqTimeLin =
  record {
    cat = seqTimeCat;
    first = F.id;
    swap = 0;
    assoc = 0;
    <tt,id> = 0;
    snd<tt,> = 0;
    <_×_> = _+_;
    second = F.id;
    tt→[] = 0;
    []→tt = 0;
    <∷> = 0;
    uncons = 0 }

seqTimeRewiring : Rewiring TimeCost
seqTimeRewiring =
  record {
    linRewiring = seqTimeLin;
    tt = 0;
    dup = 0;
    <[]> = 0;
    <_,_> = _+_;
    fst = 0;
    snd = 0;
    rewire = const 0;
    rewireTbl = const 0 }

seqTimeFork : HasFork TimeCost
seqTimeFork = record { cond = 1; fork = 1+_+_ }

seqTimeOps : FunOps TimeCost
seqTimeOps = record { rewiring = seqTimeRewiring; hasFork = seqTimeFork;
                      <0b> = 0; <1b> = 0 }

seqTimeBij : Bijective TimeCost
seqTimeBij = FunOps.bijective seqTimeOps

timeCat : Category (λ _ _ → Time)
timeCat = seqTimeCat

timeLin : LinRewiring TimeCost
timeLin =
  record {
    cat = timeCat;
    first = F.id;
    swap = 0;
    assoc = 0;
    <tt,id> = 0;
    snd<tt,> = 0;
    <_×_> = _⊔_;
    second = F.id;
    tt→[] = 0;
    []→tt = 0;
    <∷> = 0;
    uncons = 0 }

timeRewiring : Rewiring TimeCost
timeRewiring =
  record {
    linRewiring = timeLin;
    tt = 0;
    dup = 0;
    <[]> = 0;
    <_,_> = _⊔_;
    fst = 0;
    snd = 0;
    rewire = const 0;
    rewireTbl = const 0 }

timeFork : HasFork TimeCost
timeFork = record { cond = 1; fork = 1+_⊔_ }

timeOps : FunOps TimeCost
timeOps = record { rewiring = timeRewiring; hasFork = timeFork;
                   <0b> = 0; <1b> = 0 }

{-
timeOps≡seqTimeOps : timeOps ≡ record seqTimeOps {
                                rewiring = record seqTimeRewiring {
                                             linRewiring = record seqTimeLin { <_×_> = _⊔_ };
                                             <_,_> = _⊔_};
                                fork = 1+_⊔_ }
                                {-;
                                <∷> = 0; uncons = 0 } -- Without <∷> = 0... this definition makes
                                                       -- the FunOps record def yellow
                                                       -}
timeOps≡seqTimeOps = ≡.refl
-}

{-
open import maxsemiring
open ⊔-+-SemiringSolver
timeOps' : ∀ n → FunOps (constFuns (Polynomial n))
timeOps' n = record {
            id = con 0; _∘_ = _:*_;
            <0b> = con 0; <1b> = con 0; cond = con 1; fork = 1+_+_; tt = con 0;
            <_,_> = _:*_; fst = con 0; snd = con 0;
            dup = con 0; <_×_> = _:+_; swap = con 0; assoc = con 0;
            <tt,id> = con 0; snd<tt,> = con 0;
            <[]> = con 0; <∷> = con 0; uncons = con 0 }
   where 1+_+_ : Polynomial n → Polynomial n → Polynomial n
         1+ x + y = con 1 :* (x :* y)

Module TimeOps' where
  Time = ℕ
  open FunOps (timeOps' 1) public

  snoc≡0 : ∀ n → snoc {n} := con 0
  snoc≡0 zero = ?
  snoc≡0 (suc n) = ?
-}

module TimeOps where
  open FunOps timeOps public

  snoc≡0 : ∀ n → snoc {n} ≡ 0
  snoc≡0 zero = ≡.refl
  snoc≡0 (suc n) rewrite snoc≡0 n = ≡.refl

  reverse≡0 : ∀ n → reverse {n} ≡ 0
  reverse≡0 zero = ≡.refl
  reverse≡0 (suc n) rewrite snoc≡0 n | reverse≡0 n = ≡.refl

  foldl≡* : ∀ m n → foldl {m} n ≡ m * n
  foldl≡* zero n = ≡.refl
  foldl≡* (suc m) n rewrite foldl≡* m n
                          | ⊔°.+-comm n 0
                          | ℕ°.+-comm (m * n + n) 0
                          | ℕ°.+-comm (m * n + n) 0
                          | ℕ°.+-comm (m * n) n
                          = ≡.refl

  replicate≡0 : ∀ n → replicate {n} ≡ 0
  replicate≡0 zero = ≡.refl
  replicate≡0 (suc n) = replicate≡0 n

  constBit≡0 : ∀ b → constBit b ≡ 0
  constBit≡0 true  = ≡.refl
  constBit≡0 false = ≡.refl

  maximum : ∀ {n} → Vec ℕ n → ℕ
  maximum = V.foldr (const ℕ) (λ {_} x y → x ⊔ y) 0

  constVec⊤≡maximum : ∀ {n b} {B : Set b} (f : B → Time) xs → constVec⊤ {n} f xs ≡ maximum (V.map f xs)
  constVec⊤≡maximum f [] = ≡.refl
  constVec⊤≡maximum {suc n} f (b ∷ bs) rewrite ℕ°.+-comm (f b ⊔ constVec⊤ f bs) 0
                                              | constVec⊤≡maximum f bs = ≡.refl

  constBits≡0 : ∀ {n} xs → constBits {n} xs ≡ 0
  constBits≡0 [] = ≡.refl
  constBits≡0 {suc n} (b ∷ bs) rewrite constBit≡0 b
                                     | constBits≡0 bs = ≡.refl

  fromBitsFun≡i : ∀ {i o} (f : i →ᵇ o) → fromBitsFun f ≡ i
  fromBitsFun≡i {zero}  f rewrite constBits≡0 (f []) = ≡.refl
  fromBitsFun≡i {suc i} f rewrite fromBitsFun≡i {i} (f ∘′ 1∷_)
                                | fromBitsFun≡i {i} (f ∘′ 0∷_)
                                | ℕ°.+-comm (i ⊔ i) 0
                                = ≡.cong suc (i⊔i≡i i)

                                {-
spaceLin : LinRewiring SpaceCost
spaceLin =
  record {
    id = 0;
    _∘_ = _+_;
    first = F.id;
    swap = 0;
    assoc = 0;
    <tt,id> = 0;
    snd<tt,> = 0;
    <_×_> = _+_;
    second = F.id;
    tt→[] = 0;
    []→tt = 0;
    <∷> = 0;
    uncons = 0 }

spaceLin≡seqTimeLin : spaceLin ≡ seqTimeLin
spaceLin≡seqTimeLin = ≡.refl

spaceRewiring : Rewiring TimeCost
spaceRewiring =
  record {
    linRewiring = spaceLin;
    tt = 0;
    dup = 1;
    <[]> = 0;
    <_,_> = 1+_+_;
    fst = 0;
    snd = 0;
    rewire = λ {_} {o} _ → o;
    rewireTbl = λ {_} {o} _ → o }

spaceFork : HasFork SpaceCost
spaceFork = record { cond = 1; fork = 1+_+_ }

spaceOps : FunOps SpaceCost
spaceOps = record { rewiring = spaceRewiring; hasFork = spaceFork;
                    <0b> = 1; <1b> = 1 }

             {-
-- So far the space cost model is like the sequential time cost model but makes <0b>,<1b>,dup
-- cost one unit of space.
spaceOps≡seqTimeOps : spaceOps ≡ record seqTimeOps { <0b> = 1; <1b> = 1; dup = 1; <_,_> = 1+_+_
                                                    ; <∷> = 0; uncons = 0 } -- same bug here
spaceOps≡seqTimeOps = ≡.refl
-}

module SpaceOps where
  open FunOps spaceOps public

  snoc≡0 : ∀ n → snoc {n} ≡ 0
  snoc≡0 zero = ≡.refl
  snoc≡0 (suc n) rewrite snoc≡0 n = ≡.refl

  reverse≡0 : ∀ n → reverse {n} ≡ 0
  reverse≡0 zero = ≡.refl
  reverse≡0 (suc n) rewrite snoc≡0 n | reverse≡0 n = ≡.refl

  foldl≡* : ∀ m n → foldl {m} n ≡ m * n
  foldl≡* zero n = ≡.refl
  foldl≡* (suc m) n rewrite foldl≡* m n
                          | ℕ°.+-comm n 0
                          | ℕ°.+-comm (m * n + n) 0
                          | ℕ°.+-comm (m * n + n) 0
                          | ℕ°.+-comm (m * n) n
                          = ≡.refl

  replicate≡n : ∀ n → replicate {n} ≡ n
  replicate≡n zero = ≡.refl
  replicate≡n (suc n) rewrite replicate≡n n = ≡.refl

  constBit≡1 : ∀ b → constBit b ≡ 1
  constBit≡1 true  = ≡.refl
  constBit≡1 false = ≡.refl

  constVec⊤≡sum : ∀ {n b} {B : Set b} (f : B → Space) xs → constVec⊤ {n} f xs ≡ V.sum (V.map f xs)
  constVec⊤≡sum f [] = ≡.refl
  constVec⊤≡sum {suc n} f (b ∷ bs) rewrite ℕ°.+-comm (f b + constVec⊤ f bs) 0
                                          | constVec⊤≡sum f bs = ≡.refl

  constVec≡sum : ∀ {n b} {B : Set b} (f : B → Space) xs → constVec {n} f xs ≡ V.sum (V.map f xs)
  constVec≡sum f xs rewrite constVec⊤≡sum f xs | ℕ°.+-comm (V.sum (V.map f xs)) 0 = ≡.refl

  constBits≡n : ∀ {n} xs → constBits {n} xs ≡ n
  constBits≡n [] = ≡.refl
  constBits≡n {suc n} (b ∷ bs) rewrite constBit≡1 b
                                     | constBits≡n bs
                                     | ℕ°.+-comm n 0 = ≡.refl

  fromBitsFun-cost : ∀ (i o : ℕ) → ℕ
  fromBitsFun-cost zero    o = o
  fromBitsFun-cost (suc i) o = 1 + 2*(fromBitsFun-cost i o)

  fromBitsFun≡ : ∀ {i o} (f : i →ᵇ o) → fromBitsFun f ≡ fromBitsFun-cost i o
  fromBitsFun≡ {zero}  {o} f rewrite constBits≡n (f []) | ℕ°.+-comm o 0 = ≡.refl
  fromBitsFun≡ {suc i} {o} f rewrite fromBitsFun≡ {i} (f ∘′ 1∷_)
                                   | fromBitsFun≡ {i} (f ∘′ 0∷_)
                                   | ℕ°.+-comm (2* (fromBitsFun-cost i o)) 0
                                   = ≡.refl

{-
time×spaceOps : FunOps (constFuns (ℕ × ℕ))
time×spaceOps = ×⊤-Ops timeOps spaceOps

module Time×SpaceOps = FunOps time×spaceOps
-}
-- -}
-- -}
-- -}
-- -}
