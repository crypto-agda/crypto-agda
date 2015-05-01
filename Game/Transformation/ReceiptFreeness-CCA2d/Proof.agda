{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Nat
open import Data.Vec hiding (_>>=_ ; _∈_)
open import Data.List as L
open import Data.Fin as Fin using (Fin)
open import Relation.Binary.PropositionalEquality.NP as ≡ using (_≡_; _≗_; ap₂; refl; !_; _∙_; ap; module ≡-Reasoning)
open import Control.Strategy renaming (map to mapS)
open import Control.Strategy.Utils
open import Crypto.Schemes
open import Game.Challenge
import Game.ReceiptFreeness
import Game.IND-CCA2-dagger.Experiment
import Game.IND-CPA-utils
import Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst

import Data.List.Any
open Data.List.Any using (here; there)
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

module Game.Transformation.ReceiptFreeness-CCA2d.Proof
  (pke : Pubkey-encryption)
  (open Pubkey-encryption pke)
  (SerialNumber : Type)
  (Rₐ : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  (𝟚→Message→𝟚 : ∀ m → Message→𝟚 (just (𝟚→Message m)) ≡ m)
  (#q : ℕ) (max#q : Fin #q)
  (Check    : let open Game.ReceiptFreeness pke SerialNumber Rₐ 𝟚→Message Message→𝟚 #q max#q
               in BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → fst (snd r) ∉ L.map (fst ∘ snd) bb)
  -- (CheckEnc : ∀ pk m rₑ → Check (enc pk m rₑ) ≡ 1₂)
  where

functionally-correct' : ∀ rₖ rₑ m → let pk , sk = key-gen rₖ in Message→𝟚 (dec sk (enc pk (𝟚→Message m) rₑ)) ≡ m
functionally-correct' rₖ rₑ m rewrite functionally-correct rₖ rₑ (𝟚→Message m) = 𝟚→Message→𝟚 m

cons= : ∀ {a} {A : Type_ a}{x x' : A}{xs xs' : List A}(px : x ≡ x')(pxs : xs ≡ xs') → (x List.∷ xs) ≡ (x' ∷ xs')
cons= = ap₂ _∷_

module RFSim = Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst pke SerialNumber Rₐ 𝟚→Message Message→𝟚 #q max#q Check
  hiding (module CCA2†)

open RFSim using (Rₐ† ; CCAProto ; RFProto; module Simulator ; MITMState ; module Receipts)

open Game.IND-CPA-utils Message CipherText
module RF = Game.ReceiptFreeness pke SerialNumber Rₐ 𝟚→Message Message→𝟚 #q max#q
module RFC = RF.Experiment Check
open RFC
open RF renaming (Phase to RFPhase; Q to RFQ; Resp to RFResp)
open StatefulRun

module CCA2† = Game.IND-CCA2-dagger.Experiment pke Rₐ†

DecRoundChallenger : (Next : Type) → Type
DecRoundChallenger = Server CCAProto

module SimulatorProof
  (RFA : RF.Adversary)
  (rₖ : Rₖ)(rₐ : Rₐ)(rgb : Rgb ²)
  (rgbs : PhaseNumber → Vec Rgb #q) (sn : SerialNumber ²)
  (ext𝟚 : ∀ {A : Type} {f g : 𝟚 → A} → f ≗ g → f ≡ g)

  -- Secret random bit
  (b : 𝟚) where

  k  = key-gen rₖ
  pk = fst k
  sk = snd k

  module Sim = Simulator RFA
  module Tr = Sim.SecondLayer rgbs pk
  open Tr using (ballot; hack-challenge; MITM-phase)
  open Sim.AdversaryParts rgbs pk rₐ using (A†1; A†2; A†3)
  A† = Sim.A†

  rₑ = snd ∘ snd ∘ rgb

  module RFEXP = RFC.EXP b RFA pk sk rₐ rgbs rₑ
  module EXP†  = CCA2†.EXP b A† (rₐ , rgbs) pk sk rₑ

  open RFEXP using (BBrfc; Aphase1; Aphase2; BBphase1; AdversaryRFChallenge)

  open RFC.OracleS sk pk rgbs

  module _ {X} (p# : PhaseNumber) where
    RX : X × S → MITMState X → Type
    RX (x , bb , _) (x' , bb' , ta) = bb ≡ bb' × x ≡ x' × ta ≡ tally sk bb'

    Bisim' : (n : Fin #q) (bb : BB) → Client RFProto X → Client CCAProto (MITMState X) → Type
    Bisim' n bb clt0 clt1 = RX (runS (OracleS p#) clt0 (bb , n)) (run (dec sk) clt1)

    pf-phase : (n : Fin #q) (bb : BB) (clt : Client _ _)
                   → Bisim' n bb clt (mitm-to-client-trans (Tr.MITM-phase p# n bb (tally sk bb)) clt)
    pf-phase n bb (ask REB cont) = pf-phase (Fin.pred n) bb (cont (Tr.ballot p# n))
    pf-phase n bb (ask RBB cont) = pf-phase (Fin.pred n) bb (cont bb)
    pf-phase n bb (ask RTally cont) = pf-phase (Fin.pred n) bb (cont (tally sk bb))
    pf-phase n bb (ask (RCO (m? , sn , enc-co)) cont) = pf-phase (Fin.pred n) bb (cont (Message→𝟚 (dec sk enc-co)))
    pf-phase n bb (ask (Vote r) cont) with Check bb r -- (enc-co r)
    ... | 0₂ = pf-phase (Fin.pred n) bb (cont reject)
    ... | 1₂ = pf-phase (Fin.pred n) (r ∷ bb) (cont accept)
    pf-phase n bb (done x) = refl , refl , refl

  pf-phase1 : Bisim' 0₂ max#q [] Aphase1 A†1
  pf-phase1 = pf-phase 0₂ max#q [] Aphase1

  MITM1 : MITMState _
  MITM1 = run (dec sk) A†1
  MITM-S1 : _
  MITM-S1 = snd MITM1
  MITM-BB1 : BB
  MITM-BB1 = fst MITM-S1
  MITM-tally1 : Tally
  MITM-tally1 = snd MITM-S1

  tally1 = tally sk BBphase1

  BBphase1-pf : BBphase1 ≡ MITM-BB1
  BBphase1-pf = fst pf-phase1

  -- unused
  CPA†Challenge : CPA†Adversary (RFPhase Candidate × Receipt ²)
  CPA†Challenge = Tr.hack-challenge AdversaryRFChallenge

  tally-pf : tally sk BBrfc ≡ (1 , 1) +,+ tally1
  tally-pf rewrite
             functionally-correct' rₖ (snd (snd (rgb 0₂))) b
           | functionally-correct' rₖ (snd (snd (rgb 1₂))) (not b)
           with not b
  ... | 0₂ = refl
  ... | 1₂ = refl

  tally1-pf : tally1 ≡ MITM-tally1
  tally1-pf rewrite BBphase1-pf = !(snd (snd pf-phase1))

  tally1-pf' : tally sk BBrfc ≡ (1 , 1) +,+ MITM-tally1
  tally1-pf' = tally-pf ∙ ap (_+,+_ (1 , 1)) tally1-pf

  A†4 : BB → _
  A†4 bb = Tr.decRoundAdv2 bb ((1 , 1) +,+ MITM-tally1)

  pf-phase2 : Bisim' 1₂ max#q BBrfc Aphase2 (A†4 BBrfc Aphase2)
  pf-phase2 rewrite ! tally1-pf' = pf-phase 1₂ max#q BBrfc Aphase2
  -- TODO it might be convenient to rewrite the BB equalities here as well

  pf-A† : run (dec sk) (A† (rₐ , rgbs) pk) ≡ A†2 (run (dec sk) A†1)
  pf-A† = run-map (dec sk) A†2 A†1

  open ≡-Reasoning
  open Receipts 0₂

  put-c = put-resp (Tr.hack-challenge (fst (run (dec sk) A†1))) EXP†.c
  MITM-phase2 = fst put-c
  MITM-receipts = snd put-c
  MITM-bb-rfc = MITM-receipts ∷² MITM-BB1

  sn' = get-chal (fst (runS (OracleS 0₂) Aphase1 ([] , max#q)))

  E = enc pk
  D = dec sk

  ct-pf : ∀ i → EXP†.c i ≡ (E ∘ 𝟚→Message ∘ flip _xor_ b ˢ rₑ) i
  ct-pf i = ap (λ x → E (get-chal x (i xor b)) (snd (snd (rgb i)))) pf-A†

  Aphase2-pf : Aphase2 ≡ MITM-phase2
  Aphase2-pf = ap₂ (λ rfc ct → put-resp rfc (receipts (get-chal rfc) ct))
                   (fst (snd pf-phase1))
                   (ext𝟚 (!_ ∘ ct-pf))

  receipts-pf : RFEXP.receipts ≗ receipts sn' EXP†.c
  receipts-pf i = ap (λ x → marked 0₂ , sn' i , x) (! ct-pf i)

  BBrfc-pf = BBrfc
           ≡⟨ cons= (receipts-pf 0₂)
             (cons= (receipts-pf 1₂) (fst pf-phase1)) ⟩
             receipts sn' EXP†.c ∷² MITM-BB1
           ≡⟨ ap (λ x → receipts (get-chal x) EXP†.c ∷² MITM-BB1)
                 (fst (snd pf-phase1)) ⟩
             MITM-bb-rfc
           ∎

  pf-b′ : RFEXP.b′ ≡ EXP†.b'
  pf-b′ = RFEXP.b′
        ≡⟨by-definition⟩
          fst (runS (OracleS 1₂) Aphase2 (BBrfc , max#q))
        ≡⟨ fst (snd pf-phase2) ⟩
          fst (run D (A†4 BBrfc Aphase2))
        ≡⟨ ap (λ bb → fst (run D (A†4 bb Aphase2))) BBrfc-pf ⟩
          fst (run D (A†4 MITM-bb-rfc Aphase2))
        ≡⟨ ap (fst ∘ run D ∘ A†4 MITM-bb-rfc) Aphase2-pf ⟩
          fst (run D (A†4 MITM-bb-rfc MITM-phase2))
        ≡⟨ ! run-map D fst (A†4 MITM-bb-rfc MITM-phase2) ⟩
          run D (mapS fst (A†4 MITM-bb-rfc MITM-phase2))
        ≡⟨by-definition⟩
          run D (put-resp (A†2 (run D A†1)) EXP†.c)
        ≡⟨ ap (λ x → run D (put-resp x EXP†.c)) (! pf-A†) ⟩
          run D (put-resp (run D (A† (rₐ , rgbs) pk)) EXP†.c)
        ≡⟨by-definition⟩
          EXP†.b'
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
