{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.One
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
  record Proto : ★₁ where
    constructor P[_,_]
    field
      Q : ★
      R : Q → ★

  Client : Proto → ★ → ★
  Client P[ Q , R ] A = Strategy Q R A

  {-
  data Bisim {P P' A A'} (RA : A → A' → ★) : Client P A → Client P' A' → ★ where
    ask-nop : ∀ {q? cont clt} r
              → Bisim RA (cont r) clt
              → Bisim RA (ask q? cont) clt
    ask-ask : ∀ q₀ q₁ cont₀ cont₁ r₀ r₁
              → ({!!} → Bisim RA (cont₀ r₀) (cont₁ r₁))
              → Bisim RA (ask q₀ cont₀) (ask q₁ cont₁)
-}
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

  record ServerResp (P : Proto) (q : Proto.Q P) (A : ★₀) : ★₀ where
    coinductive
    open Proto P
    field
        srv-resp : R q
        srv-cont : ∀ q → ServerResp P q A
  open ServerResp

  Server : Proto → ★₀ → ★₀
  Server P A = ∀ q → ServerResp P q A

  OracleServer : Proto → ★₀
  OracleServer P[ Q , R ] = (q : Q) → R q
 
  module _ {P : Proto} {A : ★} where
    open Proto P
    com : Server P A → Client P A → A
    com srv (ask q κc) = com (srv-cont r) (κc (srv-resp r)) where r = srv q
    com srv (done x)   = x

  module _ (P P' : Proto) (A A' : ★) where
    module P = Proto P
    module P' = Proto P'
    record MITM : ★ where
      coinductive
      field
        hack-query : (q' : P'.Q) → Client P (P'.R q' × MITM)
        hack-result : A' → Client P A
    open MITM

    module WithOutBind where
        hacked-com-client : Server P A → MITM → Client P' A' → A
        hacked-com-mitm : ∀ {q'} → Server P A → Client P (P'.R q' × MITM) → (P'.R q' → Client P' A') → A
        hacked-com-srv-resp : ∀ {q q'} → ServerResp P q A → (P.R q → Client P (P'.R q' × MITM)) → (P'.R q' → Client P' A') → A

        hacked-com-srv-resp r mitm clt = hacked-com-mitm (srv-cont r) (mitm (srv-resp r)) clt

        hacked-com-mitm srv (ask q? mitm) clt = hacked-com-srv-resp (srv q?) mitm clt
        hacked-com-mitm srv (done (r' , mitm)) clt = hacked-com-client srv mitm (clt r')

        hacked-com-client srv mitm (ask q' κc) = hacked-com-mitm srv (hack-query mitm q') κc
        hacked-com-client srv mitm (done x) = com srv (hack-result mitm x)

    mitm-to-client-trans : MITM → Client P' A' → Client P A
    mitm-to-client-trans mitm (ask q? cont) = hack-query mitm q? >>= λ { (r' , mitm') → mitm-to-client-trans mitm' (cont r') }
    mitm-to-client-trans mitm (done x)      = hack-result mitm x

    hacked-com : Server P A → MITM → Client P' A' → A
    hacked-com srv mitm clt = com srv (mitm-to-client-trans mitm clt)

  module _ (P : Proto) (A : ★) where
    open Proto P
    open MITM
    honest : MITM P P A A
    hack-query  honest q = ask q λ r → done (r , honest)
    hack-result honest a = done a

  module _ (P : Proto) (A : ★) (Oracle : OracleServer P) where
    oracle-server : Server P A
    srv-resp (oracle-server q) = Oracle q
    srv-cont (oracle-server q) = oracle-server

Message = 𝟚
open Game.IND-CPA-utils Message CipherText
module RF    = Game.ReceiptFreeness PubKey SecKey         CipherText SerialNumber Rₑ Rₖ Rₐ  #q max#q KeyGen Enc Dec Check CheckEnc
open RF renaming (Phase to RFPhase; Q to RFQ; Resp to RFResp)

Rₐ† : ★
Rₐ† = Rₐ × {-SerialNumber ² ×-} (Vec Rgb #q)²
module CCA2† = Game.IND-CCA2-dagger PubKey SecKey Message CipherText              Rₑ Rₖ Rₐ†          KeyGen Enc Dec

CPAChallenger : (Next : ★) → ★
CPAChallenger Next = Message ² → CipherText ² × Next

CCAProto : Proto
CCAProto = P[ CipherText , const Message ]

RFProto : Proto
RFProto = P[ RFQ , RFResp ]

DecRoundChallenger : (Next : ★) → ★
DecRoundChallenger = Server CCAProto

module AdversaryTrans (m : 𝟚 {-which mark to put on the two receipts-})
                      (RFA : RF.Adversary) (rₐ : Rₐ) --(sn : SerialNumber ²)
                      (rgb : (Vec Rgb #q)²) (pk : PubKey) where
  open MITM

  {-
  askDecBB : BB → DecRound ClearBB
  askDecBB [] = done []
  askDecBB ((m? , sn , enc-co) ∷ bb) = ask enc-co (λ co → askDecBB bb >>= λ dec-bb → done ((co , m?) ∷ dec-bb))
  -}

  MITMState : ★ → ★
  MITMState X = X × BB × Tally

  ballot : RF.PhaseNumber → Fin #q → Ballot
  ballot p# n = RF.genBallot pk (lookup n (rgb p#))

  mitmPhase : (p# : RF.PhaseNumber) → Fin #q → BB → Tally → ∀ {X} → MITM CCAProto RFProto (MITMState X) X
  hack-query (mitmPhase p# n bb ta) REB = done (ballot p# n , mitmPhase p# (Fin.pred n) bb ta)
  hack-query (mitmPhase p# n bb ta) RBB = done (bb , mitmPhase p# (Fin.pred n) bb ta)
  hack-query (mitmPhase p# n bb ta) RTally = done (ta , mitmPhase p# (Fin.pred n) bb ta)
  hack-query (mitmPhase p# n bb ta) (RCO (m? , sn , enc-co)) =
     -- if receipt in DB then ...
     ask enc-co λ co → done (co , mitmPhase p# (Fin.pred n) bb ta)
  hack-query (mitmPhase p# n bb ta) (Vote (m? , sn , enc-co))
     -- lots of cases
     = ask enc-co λ co →
         let (res , cbb' , bb') =
                case Check enc-co
                  0: (RF.reject ,′ ta , bb)
                  1: (RF.accept , tallyMarkedReceipt? co m? +,+ ta , (m? , sn , enc-co) ∷ bb) in
         done (res , mitmPhase p# (Fin.pred n) bb' cbb')
  hack-result (mitmPhase p# n bb ta) r = done (r , bb , ta)

  MITM-RFChallenge : ∀ {X} → MITM _ _ (MITMState X) X
  MITM-RFChallenge = mitmPhase 0₂ max#q [] (0 , 0)

  decRoundAdvTr : ∀ {X} → Client RFProto X → Client CCAProto (MITMState X)
  decRoundAdvTr = mitm-to-client-trans _ _ _ _ MITM-RFChallenge

  decRoundAdv1 : Client CCAProto (MITMState (RFChallenge (RFPhase Candidate)))
  decRoundAdv1 = decRoundAdvTr (RFA rₐ pk)

  module Receipts (sn : SerialNumber ²) (ct : CipherText ²) where
      receipts : Candidate → Receipt
      receipts c = marked m , sn c , ct c


{-
      trCBB : ClearBB → ClearBB
      trCBB cbb = ? ∷ ? ∷
      -}

      trBB : BB → BB
      trBB bb = receipts 0₂ ∷ receipts 1₂ ∷ bb

  hack-challenge : ∀ {X} → RFChallenge X → CPA†Adversary (X × (BB → BB))
  get-m (hack-challenge _) = alice-then-bob , bob-then-alice
  put-c (hack-challenge rfc) c₀ c₁ = proj₂ rfc receipts , trBB
    where
      ct = proj (c₀ , c₁)
      open Receipts (proj₁ rfc) ct

  module _ (bb : BB) (ta : Tally) (Aphase[II] : RFPhase Candidate) where

    decRoundAdv2 : DecRound (MITMState Candidate)
    decRoundAdv2 = mitm-to-client-trans _ _ _ _ (mitmPhase 1₂ max#q bb ta) Aphase[II]

  mapCPAAdv = TransformAdversaryResponse.A*

  A† : DecRound (CPA†Adversary (DecRound 𝟚))
  A† = decRoundAdv1 >>= λ { (rfc , bb , ta) →
         done (mapCPAAdv (λ f c → decRoundAdv2 (proj₂ (f c) bb) ((1 , 1) +,+ ta) (proj₁ (f c)) >>= (done ∘ proj₁))
                  (hack-challenge rfc)) }

A†-trans : ∀ m → RF.Adversary → CCA2†.Adversary
A†-trans m RFA (rₐ , rgb) pk = AdversaryTrans.A† m RFA rₐ rgb pk

open StatefulRun
module Pfff
  {-(b : 𝟚)-} (RFA : RF.Adversary) (pk : PubKey) (sk : SecKey)
  (DecEnc : ∀ rₑ m → Dec sk (Enc pk m rₑ) ≡ m)
  (rₐ : Rₐ) (rgb : Candidate → Rgb) -- (rco : Candidate → CO) (rₑ : Candidate → Rₑ)
  (rgbs : PhaseNumber → Vec Rgb #q) (sn : Candidate → SerialNumber) where

  postulate b m : 𝟚
  {-
  b = 0₂
  t = 0₂
  m = 0₂
  -}
  module Tr = AdversaryTrans m RFA rₐ {-sn-} rgbs pk

  rₑ = proj₂ ∘ proj₂ ∘ rgb

  module RFEXP = RF.EXP b RFA pk sk rₐ rgbs (Enc pk ˢ rₑ) (const (marked 0₂))
  module EXP†  = CCA2†.EXP b (A†-trans m RFA) (rₐ , {-sn ,-} rgbs) pk sk (rₑ 0₂) (rₑ 1₂)

  module _ {X} (p# : PhaseNumber) where
    RX : X × RFEXP.S → Tr.MITMState X → ★
    RX (x , bb , _) (x' , bb' , _) = bb ≡ bb' × x ≡ x'

    Bisim' : (n : Fin #q) (bb : BB) → Client RFProto X → Client CCAProto (Tr.MITMState X) → ★
    Bisim' n bb clt0 clt1 = RX (runS (RFEXP.OracleS p#) clt0 (bb , n)) (run (Dec sk) clt1)

    pf-phase : (n : Fin #q) (bb : BB) (clt : Client _ _)
                   → Bisim' n bb clt (mitm-to-client-trans _ _ _ _ (Tr.mitmPhase p# n bb (tally sk bb)) clt)
    pf-phase n bb (ask REB cont) = pf-phase (Fin.pred n) bb (cont (Tr.ballot p# n))
    pf-phase n bb (ask RBB cont) = pf-phase (Fin.pred n) bb (cont bb)
    pf-phase n bb (ask RTally cont) = pf-phase (Fin.pred n) bb (cont (tally sk bb))
    pf-phase n bb (ask (RCO (m? , sn , enc-co)) cont) = pf-phase (Fin.pred n) bb (cont (Dec sk enc-co))
    pf-phase n bb (ask (Vote r) cont) with Check (enc-co r)
    ... | 0₂ = pf-phase (Fin.pred n) bb (cont reject)
    ... | 1₂ = pf-phase (Fin.pred n) (r ∷ bb) (cont accept)
    pf-phase n bb (done x) = refl , refl

  pf-phase[I] : Bisim' 0₂ max#q [] RFEXP.Aphase[I] Tr.decRoundAdv1
  pf-phase[I] = pf-phase 0₂ max#q [] RFEXP.Aphase[I]

  tally[I] = tally sk RFEXP.BBphase[I]

  CPA†Challenge : CPA†Adversary (RFPhase Candidate × (BB → BB))
  CPA†Challenge = Tr.hack-challenge RFEXP.AdversaryRFChallenge

  tally-pf : tally sk RFEXP.BBrfc ≡ (1 , 1) +,+ tally[I]
  tally-pf rewrite
             DecEnc (proj₂ (proj₂ (rgb 0₂))) 0₂
           | DecEnc (proj₂ (proj₂ (rgb 1₂))) 1₂
           = refl

  pf-phase[II] : Bisim' 1₂ max#q RFEXP.BBrfc RFEXP.Aphase[II] (Tr.decRoundAdv2 RFEXP.BBrfc (tally sk RFEXP.BBrfc) RFEXP.Aphase[II])
  pf-phase[II] = pf-phase 1₂ max#q RFEXP.BBrfc RFEXP.Aphase[II]

  pf-phase[II]' : Bisim' 1₂ max#q RFEXP.BBrfc RFEXP.Aphase[II] (Tr.decRoundAdv2 RFEXP.BBrfc ((1 , 1) +,+ tally[I]) RFEXP.Aphase[II])
  pf-phase[II]' rewrite sym tally-pf = pf-phase[II]

  {-
  module DecRoundAdv2 = Tr.DecRoundAdv2 RFEXP.BBphase[I] CBB[I] RFEXP.AdversaryRFChallenge

--  msg = DecRoundAdv2.get-m

  ct = enc-co ∘ RFEXP.receipts

  {-

  pf-b′ : RFEXP.b′ ≡ EXP†.b′
  pf-b′ = {!!}

  {-
  pf-chal : ∀ c → RFEXP.randomly-swapped-receipts c ≡ DecRoundAdv2.ContA.randomly-swapped-receipts ([0: {!!} 1: Enc pk m (rₑ (b xor 1₂)) ]) c
  pf-chal 1₂ = {!!}
  pf-chal 0₂ = {!!}

{-

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
