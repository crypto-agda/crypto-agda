{-# OPTIONS --copatterns #-}
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Vec hiding (_>>=_ ; _∈_)
open import Data.List as L
open import Data.Fin as Fin using (Fin)
open import Relation.Binary.PropositionalEquality.NP as ≡
open import Control.Strategy renaming (map to mapS)
open import Control.Strategy.Utils
open import Game.Challenge
import Game.ReceiptFreeness
import Game.IND-CCA2-dagger
import Game.IND-CPA-utils
import Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst

import Data.List.Any
open Data.List.Any using (here; there)
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

module Game.Transformation.ReceiptFreeness-CCA2d.Proof
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
  (Check    : let open Game.ReceiptFreeness PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec
               in BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → proj₁ (proj₂ r) ∉ L.map (proj₁ ∘ proj₂) bb)
  -- (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)
  where

_²' : ★ → ★
X ²' = X × X

module RFSim = Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec Check hiding (module CCA2†)

open RFSim using (Message ; Rₐ† ; CCAProto ; RFProto; module Simulator ; MITMState ; module Receipts)

open Game.IND-CPA-utils Message CipherText
module RF = Game.ReceiptFreeness PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ  #q max#q KeyGen Enc Dec
module RFC = RF.Experiment Check
open RFC
open RF renaming (Phase to RFPhase; Q to RFQ; Resp to RFResp)
open StatefulRun

module CCA2† = Game.IND-CCA2-dagger PubKey SecKey Message CipherText Rₑ Rₖ Rₐ† KeyGen Enc Dec

DecRoundChallenger : (Next : ★) → ★
DecRoundChallenger = Server CCAProto

module SimulatorProof
  (RFA : RF.Adversary) (pk : PubKey) (sk : SecKey)
  (DecEnc : ∀ rₑ m → Dec sk (Enc pk m rₑ) ≡ m)
  (rₐ : Rₐ) (rgb : Rgb ²)
  (rgbs : PhaseNumber → Vec Rgb #q) (sn : SerialNumber ²)
  (ext𝟚 : ∀ {A : ★} {f g : 𝟚 → A} → f ≗ g → f ≡ g) where

 module PB (b : 𝟚) where

  module Sim = Simulator RFA
  module Tr = Sim.SecondLayer rgbs pk
  open Tr using (ballot; hack-challenge; MITM-phase)
  open Sim.AdversaryParts rgbs pk rₐ using (A†1; A†2; A†3)
  A† = Sim.A†

  rₑ = proj₂ ∘ proj₂ ∘ rgb

  module RFEXP = RFC.EXP b RFA pk sk rₐ rgbs rₑ
  module EXP†  = CCA2†.EXP b A† (rₐ , rgbs) pk sk rₑ

  open RFC.OracleS sk pk rgbs

  module _ {X} (p# : PhaseNumber) where
    RX : X × S → MITMState X → ★
    RX (x , bb , _) (x' , bb' , ta) = bb ≡ bb' × x ≡ x' × ta ≡ tally sk bb'

    Bisim' : (n : Fin #q) (bb : BB) → Client RFProto X → Client CCAProto (MITMState X) → ★
    Bisim' n bb clt0 clt1 = RX (runS (OracleS p#) clt0 (bb , n)) (run (Dec sk) clt1)

    pf-phase : (n : Fin #q) (bb : BB) (clt : Client _ _)
                   → Bisim' n bb clt (mitm-to-client-trans (Tr.MITM-phase p# n bb (tally sk bb)) clt)
    pf-phase n bb (ask REB cont) = pf-phase (Fin.pred n) bb (cont (Tr.ballot p# n))
    pf-phase n bb (ask RBB cont) = pf-phase (Fin.pred n) bb (cont bb)
    pf-phase n bb (ask RTally cont) = pf-phase (Fin.pred n) bb (cont (tally sk bb))
    pf-phase n bb (ask (RCO (m? , sn , enc-co)) cont) = pf-phase (Fin.pred n) bb (cont (Dec sk enc-co))
    pf-phase n bb (ask (Vote r) cont) with Check bb r -- (enc-co r)
    ... | 0₂ = pf-phase (Fin.pred n) bb (cont reject)
    ... | 1₂ = pf-phase (Fin.pred n) (r ∷ bb) (cont accept)
    pf-phase n bb (done x) = refl , refl , refl

  pf-phase1 : Bisim' 0₂ max#q [] RFEXP.Aphase1 A†1
  pf-phase1 = pf-phase 0₂ max#q [] RFEXP.Aphase1

  MITM1 : MITMState _
  MITM1 = run (Dec sk) A†1
  MITM-S1 : _
  MITM-S1 = proj₂ MITM1
  MITM-BB1 : BB
  MITM-BB1 = proj₁ MITM-S1
  MITM-tally1 : Tally
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
           with b
  ... | 0₂ = refl
  ... | 1₂ = refl

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
  open Receipts 0₂

  put-c = put-resp (Tr.hack-challenge (proj₁ (run (Dec sk) A†1))) EXP†.c
  MITM-phase2 = proj₁ put-c
  MITM-receipts = proj₂ put-c
  MITM-BB-RFC = MITM-receipts ∷² MITM-BB1

  sn' = get-chal (proj₁ (runS (OracleS 0₂) RFEXP.Aphase1 ([] , max#q)))

  ct-pf : ∀ i → EXP†.c i ≡ (Enc pk ∘ flip _xor_ b ˢ rₑ) i
  ct-pf i = ap (λ x → Enc pk (get-chal x (i xor b)) (proj₂ (proj₂ (rgb i)))) pf-A†

  receipts-pf : RFEXP.receipts ≗ receipts sn' EXP†.c
  receipts-pf i = ap (λ x → marked 0₂ , sn' i , x) (!(ct-pf i))

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
          proj₁ (runS (OracleS 1₂) RFEXP.Aphase2 (RFEXP.BBrfc , max#q))
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
