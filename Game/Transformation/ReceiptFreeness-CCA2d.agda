{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.Two
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Vec hiding (_>>=_)
open import Data.List
open import Data.Fin as Fin using (Fin)
open import Relation.Binary.PropositionalEquality.NP
open import Control.Strategy --renaming (map to mapS)
import Game.ReceiptFreeness
import Game.IND-CCA2-dagger
import Game.IND-CPA-utils

module Game.Transformation.ReceiptFreeness-CCA2d
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
  (Check    : CipherText → 𝟚)
  (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)
  where

module _ where --StrategyUtils where
  mapS : ∀ {A B Q Q' R} (f : A → B) (g : Q → Q') → Strategy Q (R ∘ g) A → Strategy Q' R B
  mapS f g (ask q cont) = ask (g q) (λ r → mapS f g (cont r))
  mapS f g (done x)     = done (f x)

  [_,_]=<<_ : ∀ {A B Q Q' R} (f : A → Strategy Q' R B) (g : Q → Q') → Strategy Q (R ∘ g) A → Strategy Q' R B
  [ f , g ]=<< ask q? cont = ask (g q?) (λ r → [ f , g ]=<< cont r)
  [ f , g ]=<< done x      = f x

  module Rec {A B Q : ★} {R : Q → ★} {M : ★ → ★}
             (runAsk : ∀ {A} → (q : Q) → (R q → M A) → M A)
             (runDone : A → M B) where
    runMM : Strategy Q R A → M B
    runMM (ask q? cont) = runAsk q? (λ r → runMM (cont r))
    runMM (done x)      = runDone x

  module MM {A B Q : ★} {R : Q → ★} {M : ★ → ★}
           (_>>=M_ : ∀ {A B : ★} → M A → (A → M B) → M B)
           (runAsk : (q : Q) → M (R q))
           (runDone : A → M B) where
    runMM : Strategy Q R A → M B
    runMM (ask q? cont) = runAsk q? >>=M (λ r → runMM (cont r))
    runMM (done x)      = runDone x

  module _ {A B Q Q' : ★} {R : Q → ★} {R'}
           (f : (q : Q) → Strategy Q' R' (R q))
           (g : A → Strategy Q' R' B) where
    [_,_]=<<'_ : Strategy Q R A → Strategy Q' R' B
    [_,_]=<<'_ (ask q? cont) = f q? >>= λ r → [_,_]=<<'_ (cont r)
    [_,_]=<<'_ (done x)      = g x

  record ServerResp {Q : ★₀} (q : Q) (R : Q → ★₀) (A : ★₀) : ★₀ where
    coinductive
    field
        srv-resp : R q
        srv-cont : ∀ q → ServerResp q R A
  open ServerResp

  Server : (Q : ★₀) (R : Q → ★₀) (A : ★₀) → ★₀
  Server Q R A = ∀ q → ServerResp q R A
 
  Client = Strategy
  module _ {Q : ★₀} (R : Q → ★₀) (A : ★₀) where
    com : Server Q R A → Client Q R A → A
    com srv (ask q κc) = com (srv-cont r) (κc (srv-resp r)) where r = srv q
    com srv (done x)   = x

  module _ (Q Q' : ★) (R : Q → ★) (R' : Q' → ★) (A A' : ★) where
    record MITM : ★ where
      coinductive
      field
        hack : (q' : Q') → Strategy Q R (R' q' × MITM)
    open MITM

    hacked-com-client : Server Q R A → MITM → Client Q' R' A' → A'
    hacked-com-mitm : ∀ {q'} → Server Q R A → Strategy Q R (R' q' × MITM) → (R' q' → Client Q' R' A') → A'
    hacked-com-srv-resp : ∀ {q q'} → ServerResp q R A → (R q → Strategy Q R (R' q' × MITM)) → (R' q' → Client Q' R' A') → A'

    hacked-com-srv-resp r mitm clt = hacked-com-mitm (srv-cont r) (mitm (srv-resp r)) clt

    hacked-com-mitm srv (ask q? mitm) clt = hacked-com-srv-resp (srv q?) mitm clt
    hacked-com-mitm srv (done (r' , mitm)) clt = hacked-com-client srv mitm (clt r')

    hacked-com-client srv mitm (done x) = x
    hacked-com-client srv mitm (ask q' κc) = hacked-com-mitm srv (hack mitm q') κc

  module _ (Q : ★) (R : Q → ★) (A : ★) where
    open MITM
    honest : MITM Q Q R R A A
    hack honest q = ask q (λ r → done (r , honest))

  module _ (Q : ★) (R : Q → ★) (A : ★) (Oracle : (q : Q) → R q) where
    oracle-server : Server Q R A
    srv-resp (oracle-server q) = Oracle q
    srv-cont (oracle-server q) = oracle-server

Message = 𝟚
open Game.IND-CPA-utils Message CipherText
module RF    = Game.ReceiptFreeness PubKey SecKey         CipherText SerialNumber Rₑ Rₖ Rₐ  #q max#q KeyGen Enc Dec Check CheckEnc
open RF using (BB; ClearBB; ClearReceipt; tallyClearBB; RFChallenge; Candidate; REB; RCO; Vote; RBB; RTally; Rgb; Ballot) renaming (Phase to RFPhase; Q to RFQ; Resp to RFResp)

_² : ★ → ★
M ² = M × M
Rₐ† : ★
Rₐ† = Rₐ × 𝟚 × (Vec Rgb #q)²
module CCA2† = Game.IND-CCA2-dagger PubKey SecKey Message CipherText              Rₑ Rₖ Rₐ†          KeyGen Enc Dec

CPAChallenger : (Next : ★) → ★
CPAChallenger Next = Message ² → CipherText ² × Next

DecRoundChallenger : (Next : ★) → ★
DecRoundChallenger = Server CipherText (const Message)

module _  (RFA : RF.Adversary) where

  A : CCA2†.Adversary
  A (rₐ , β-unused-yet , rgb) pk = {!!}
    where

      Q† = CipherText
      R† = const Message
      B† = CPAChallenger (DecRoundChallenger ((b′ : 𝟚) → 𝟚))
      Q = RFQ
      R = RFResp
      B = RFChallenge (RFPhase Candidate)
      open MITM
      DB : ★
      DB = List Ballot -- not used yet

      {-
      askDecBB : BB → DecRound ClearBB
      askDecBB [] = done []
      askDecBB ((m? , sn , enc-co) ∷ bb) = ask enc-co (λ co → askDecBB bb >>= λ dec-bb → done ((co , m?) ∷ dec-bb))
      -}

      mitmPhase : (p# : RF.PhaseNumber) → Fin #q → BB → ClearBB → DB → MITM Q† Q R† R B† B
      hack (mitmPhase p# n bb cbb db) REB = done (ballot , mitmPhase p# (Fin.pred n) bb cbb (ballot ∷ db))
        where ballot : Ballot
              ballot = RF.genBallot pk (lookup n (proj rgb p#))
      hack (mitmPhase p# n bb cbb db) RBB = done (bb , mitmPhase p# (Fin.pred n) bb cbb db)
      hack (mitmPhase p# n bb cbb db) RTally = done (tallyClearBB cbb , mitmPhase p# (Fin.pred n) bb cbb db)
      hack (mitmPhase p# n bb cbb db) (RCO (m? , sn , enc-co)) =
         -- if receipt in DB then ...
         ask enc-co λ co → done (co , mitmPhase p# (Fin.pred n) bb cbb db)
      hack (mitmPhase p# n bb cbb db) (Vote (m? , sn , enc-co))
         -- lots of cases
         = ask enc-co λ co →
             let (res , cbb') = case Check enc-co 0: (RF.reject ,′ cbb) 1: (RF.accept , (co , m?) ∷ cbb) in
             done (res , mitmPhase p# (Fin.pred n) bb cbb' db)

      MITM-RFChallenge = mitmPhase 0₂ max#q [] [] []

-- -}
-- -}
-- -}
-- -}
-- -}
