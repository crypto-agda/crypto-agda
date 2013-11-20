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
open import Control.Strategy renaming (map to mapS)
open import Game.Challenge
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

_²' : ★ → ★
X ²' = X × X

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
  module Unused where
    mapS' : ∀ {A B Q Q' R} (f : A → B) (g : Q → Q') → Strategy Q (R ∘ g) A → Strategy Q' R B
    mapS' f g (ask q cont) = ask (g q) (λ r → mapS' f g (cont r))
    mapS' f g (done x)     = done (f x)

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

  module _ {P P' : Proto} {A A' : ★} where
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
    honest : MITM {P} {P} {A} {A}
    hack-query  honest q = ask q λ r → done (r , honest)
    hack-result honest a = done a

  module _ (P : Proto) (A : ★) (Oracle : OracleServer P) where
    oracle-server : Server P A
    srv-resp (oracle-server q) = Oracle q
    srv-cont (oracle-server q) = oracle-server

Message = 𝟚
open Game.IND-CPA-utils Message CipherText
module RF = Game.ReceiptFreeness PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ  #q max#q KeyGen Enc Dec Check CheckEnc
open RF renaming (Phase to RFPhase; Q to RFQ; Resp to RFResp)

Rₐ† : ★
Rₐ† = Rₐ × (Vec Rgb #q)²
module CCA2† = Game.IND-CCA2-dagger PubKey SecKey Message CipherText Rₑ Rₖ Rₐ† KeyGen Enc Dec

CCAProto : Proto
CCAProto = P[ CipherText , const Message ]

RFProto : Proto
RFProto = P[ RFQ , RFResp ]

DecRoundChallenger : (Next : ★) → ★
DecRoundChallenger = Server CCAProto

MITMState : ★ → ★
MITMState X = X × BB × Tally

module Receipts (m : 𝟚) (sn : SerialNumber ²) (ct : CipherText ²) where
  receipts : Receipt ²
  receipts c = marked m , sn c , ct c

module Simulator (m : 𝟚 {-which mark to put on the two receipts-})
                 (RFA : RF.Adversary) where
  module SecondLayer (rgb : (Vec Rgb #q)²) (pk : PubKey) where
    open MITM

    ballot : RF.PhaseNumber → Fin #q → Ballot
    ballot p# n = RF.genBallot pk (lookup n (rgb p#))

    MITM-phase : (p# : RF.PhaseNumber) → Fin #q → BB → Tally → ∀ {X} → MITM {CCAProto} {RFProto} {MITMState X} {X}
    hack-query (MITM-phase p# n bb ta) REB = done (ballot p# n , MITM-phase p# (Fin.pred n) bb ta)
    hack-query (MITM-phase p# n bb ta) RBB = done (bb , MITM-phase p# (Fin.pred n) bb ta)
    hack-query (MITM-phase p# n bb ta) RTally = done (ta , MITM-phase p# (Fin.pred n) bb ta)
    hack-query (MITM-phase p# n bb ta) (RCO (m? , sn , enc-co)) =
       -- if receipt in DB then ...
       ask enc-co λ co → done (co , MITM-phase p# (Fin.pred n) bb ta)
    hack-query (MITM-phase p# n bb ta) (Vote (m? , sn , enc-co))
       -- lots of cases
       = ask enc-co λ co →
           let (res , cbb' , bb') =
                  case Check enc-co
                    0: (RF.reject ,′ ta , bb)
                    1: (RF.accept , tallyMarkedReceipt? co m? +,+ ta , (m? , sn , enc-co) ∷ bb) in
           done (res , MITM-phase p# (Fin.pred n) bb' cbb')
    hack-result (MITM-phase p# n bb ta) r = done (r , bb , ta)

    MITM-RFChallenge : ∀ {X} → MITM {_} {_} {MITMState X} {X}
    MITM-RFChallenge = MITM-phase 0₂ max#q [] (0 , 0)

    hack-challenge : ∀ {X} → RFChallenge X → CPA†Adversary (X × Receipt ²)
    get-chal (hack-challenge _)     = id
    put-resp (hack-challenge rfc) c = put-resp rfc receipts , receipts
      where open Receipts m (get-chal rfc) c

    module _ (bb : BB) (ta : Tally) (Aphase2 : RFPhase Candidate) where

      decRoundAdv2 : DecRound (MITMState Candidate)
      decRoundAdv2 = mitm-to-client-trans (MITM-phase 1₂ max#q bb ta) Aphase2

    mapCPAAdv = MapResponse.A*

    A†3 : BB → Tally → (RFPhase Candidate × Receipt ²) → DecRound Candidate
    A†3 bb ta (phase2 , r) = mapS proj₁ (decRoundAdv2 (r ∷² bb) ((1 , 1) +,+ ta) phase2)

    A†2 : MITMState (RFChallenge (RFPhase Candidate)) → CPA†Adversary (DecRound Candidate)
    A†2 (rfc , bb , ta) = mapCPAAdv (A†3 bb ta) (hack-challenge rfc)

  module AdversaryParts (rgb : (Vec Rgb #q)²) (pk : PubKey) (rₐ : Rₐ) where
    open SecondLayer rgb pk public
    A†1 : Client CCAProto (MITMState (RFChallenge (RFPhase Candidate)))
    A†1 = mitm-to-client-trans MITM-RFChallenge (RFA rₐ pk)

  A† : CCA2†.Adversary
  A† (rₐ , rgb) pk = mapS A†2 A†1
     where open AdversaryParts rgb pk rₐ

open StatefulRun
module SimulatorProof
  (m : 𝟚) (RFA : RF.Adversary) (pk : PubKey) (sk : SecKey)
  (DecEnc : ∀ rₑ m → Dec sk (Enc pk m rₑ) ≡ m)
  (rₐ : Rₐ) (rgb : Rgb ²)
  (rgbs : PhaseNumber → Vec Rgb #q) (sn : SerialNumber ²)
  (ext𝟚 : ∀ {A : ★} {f g : 𝟚 → A} → f ≗ g → f ≡ g) where

 module PB (b : 𝟚) where

  module Sim = Simulator m RFA
  module Tr = Sim.SecondLayer rgbs pk
  open Tr using (ballot; hack-challenge; MITM-phase)
  open Sim.AdversaryParts rgbs pk rₐ using (A†1; A†2; A†3)
  A† = Sim.A†

  rₑ = proj₂ ∘ proj₂ ∘ rgb

  module RFEXP = RF.EXP RFA pk sk rₐ rgbs (SimpleScheme.ct-resp b pk rₑ) (const (marked m))
  module EXP†  = CCA2†.EXP b A† (rₐ , rgbs) pk sk rₑ

  module _ {X} (p# : PhaseNumber) where
    RX : X × RFEXP.S → MITMState X → ★
    RX (x , bb , _) (x' , bb' , ta) = bb ≡ bb' × x ≡ x' × ta ≡ tally sk bb'

    Bisim' : (n : Fin #q) (bb : BB) → Client RFProto X → Client CCAProto (MITMState X) → ★
    Bisim' n bb clt0 clt1 = RX (runS (RFEXP.OracleS p#) clt0 (bb , n)) (run (Dec sk) clt1)

    pf-phase : (n : Fin #q) (bb : BB) (clt : Client _ _)
                   → Bisim' n bb clt (mitm-to-client-trans (Tr.MITM-phase p# n bb (tally sk bb)) clt)
    pf-phase n bb (ask REB cont) = pf-phase (Fin.pred n) bb (cont (Tr.ballot p# n))
    pf-phase n bb (ask RBB cont) = pf-phase (Fin.pred n) bb (cont bb)
    pf-phase n bb (ask RTally cont) = pf-phase (Fin.pred n) bb (cont (tally sk bb))
    pf-phase n bb (ask (RCO (m? , sn , enc-co)) cont) = pf-phase (Fin.pred n) bb (cont (Dec sk enc-co))
    pf-phase n bb (ask (Vote r) cont) with Check (enc-co r)
    ... | 0₂ = pf-phase (Fin.pred n) bb (cont reject)
    ... | 1₂ = pf-phase (Fin.pred n) (r ∷ bb) (cont accept)
    pf-phase n bb (done x) = refl , refl , refl

  pf-phase1 : Bisim' 0₂ max#q [] RFEXP.Aphase1 A†1
  pf-phase1 = pf-phase 0₂ max#q [] RFEXP.Aphase1

  MITM1 = run (Dec sk) A†1
  MITM-S1 = proj₂ MITM1
  MITM-BB1 = proj₁ MITM-S1
  MITM-tally1 = proj₂ MITM-S1

  tally1 = tally sk RFEXP.BBphase1

  BBphase1-pf : RFEXP.BBphase1 ≡ MITM-BB1
  BBphase1-pf = proj₁ pf-phase1

  -- unused
  CPA†Challenge : CPA†Adversary (RFPhase Candidate × Receipt ²)
  CPA†Challenge = Tr.hack-challenge RFEXP.AdversaryRFChallenge

  tally-pf : tally sk RFEXP.BBrfc ≡ (1 , 1) +,+ tally1
  tally-pf rewrite
             DecEnc (proj₂ (proj₂ (rgb 0₂))) b
           | DecEnc (proj₂ (proj₂ (rgb 1₂))) (not b)
           with m | b
  ... | 0₂ | 0₂ = refl
  ... | 1₂ | 1₂ = refl
  ... | 0₂ | 1₂ = refl
  ... | 1₂ | 0₂ = refl

  tally1-pf : tally1 ≡ MITM-tally1
  tally1-pf rewrite BBphase1-pf = !(proj₂ (proj₂ pf-phase1))

  tally1-pf' : tally sk RFEXP.BBrfc ≡ (1 , 1) +,+ MITM-tally1
  tally1-pf' = tally-pf ∙ ap (_+,+_ (1 , 1)) tally1-pf

  A†4 : BB → _
  A†4 bb = Tr.decRoundAdv2 bb ((1 , 1) +,+ MITM-tally1)

  pf-phase2 : Bisim' 1₂ max#q RFEXP.BBrfc RFEXP.Aphase2 (A†4 RFEXP.BBrfc RFEXP.Aphase2)
  pf-phase2 rewrite ! tally1-pf' = pf-phase 1₂ max#q RFEXP.BBrfc RFEXP.Aphase2
  -- TODO it might be convenient to rewrite the BB equalities here as well

  pf-A† : run (Dec sk) (A† (rₐ , rgbs) pk) ≡ A†2 (run (Dec sk) A†1)
  pf-A† = run-map (Dec sk) A†2 A†1

  open ≡-Reasoning
  open Receipts m

  put-c = put-resp (Tr.hack-challenge (proj₁ (run (Dec sk) A†1))) EXP†.c
  MITM-phase2 = proj₁ put-c
  MITM-receipts = proj₂ put-c
  MITM-BB-RFC = MITM-receipts ∷² MITM-BB1

  sn' = get-chal (proj₁ (runS (RFEXP.OracleS 0₂) RFEXP.Aphase1 ([] , max#q)))

  ct-pf : ∀ i → EXP†.c i ≡ (Enc pk ∘ flip _xor_ b ˢ rₑ) i
  ct-pf i = ap (λ x → Enc pk (get-chal x (i xor b)) (proj₂ (proj₂ (rgb i)))) pf-A†

  receipts-pf : RFEXP.receipts ≗ receipts sn' EXP†.c
  receipts-pf i = ap (λ x → marked m , sn' i , x) (!(ct-pf i))

  BBrfc-pf = RFEXP.BBrfc
           ≡⟨ cong₂ _∷_ (receipts-pf 0₂) (cong₂ _∷_ (receipts-pf 1₂) (proj₁ pf-phase1)) ⟩
             receipts sn' EXP†.c ∷² MITM-BB1
           ≡⟨ ap (λ x → receipts (get-chal x) EXP†.c ∷² MITM-BB1) (proj₁ (proj₂ pf-phase1)) ⟩
             MITM-BB-RFC
           ∎

  Aphase2-pf : RFEXP.Aphase2 ≡ MITM-phase2
  Aphase2-pf = cong₂ (λ rfc ct → put-resp rfc (receipts (get-chal rfc) ct)) (proj₁ (proj₂ pf-phase1)) (ext𝟚 (!_ ∘ ct-pf))

  pf-b′ : RFEXP.b′ ≡ EXP†.b′
  pf-b′ = RFEXP.b′
        ≡⟨ refl ⟩
          proj₁ (runS (RFEXP.OracleS 1₂) RFEXP.Aphase2 (RFEXP.BBrfc , max#q))
        ≡⟨ proj₁ (proj₂ pf-phase2) ⟩
          proj₁ (run (Dec sk) (A†4 RFEXP.BBrfc RFEXP.Aphase2))
        ≡⟨ ap (λ bb → proj₁ (run (Dec sk) (A†4 bb RFEXP.Aphase2))) BBrfc-pf ⟩
          proj₁ (run (Dec sk) (A†4 MITM-BB-RFC RFEXP.Aphase2))
        ≡⟨ ap (λ x → proj₁ (run (Dec sk) (A†4 MITM-BB-RFC x))) Aphase2-pf ⟩
          proj₁ (run (Dec sk) (A†4 MITM-BB-RFC MITM-phase2))
        ≡⟨ ! (run-map (Dec sk) proj₁ (A†4 MITM-BB-RFC MITM-phase2)) ⟩
          run (Dec sk) (mapS proj₁ (A†4 MITM-BB-RFC MITM-phase2))
        ≡⟨ refl ⟩
          run (Dec sk) (put-resp (A†2 (run (Dec sk) A†1)) EXP†.c)
        ≡⟨ ap (λ x → run (Dec sk) (put-resp x EXP†.c)) (! pf-A†) ⟩
          run (Dec sk) (put-resp (run (Dec sk) (A† (rₐ , rgbs) pk)) EXP†.c)
        ≡⟨ refl ⟩
          EXP†.b′
        ∎

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
