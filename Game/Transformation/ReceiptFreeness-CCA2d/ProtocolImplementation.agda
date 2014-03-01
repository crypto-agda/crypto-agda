
{-# OPTIONS --copatterns #-}
open import Type
open import Data.Fin
open import Data.Nat using (ℕ)
open import Data.One
open import Data.Product
open import Data.Two
open import Data.Vec using (Vec ; lookup)
open import Data.List using ([] ; _∷_)

import Game.ReceiptFreeness.Definitions.Encryption as Defs
import Game.ReceiptFreeness.Definitions.Receipt as Receipt
import Game.ReceiptFreeness.Definitions.Tally as Tally
import Game.ReceiptFreeness.Protocol
import Game.IND-CCA2-dagger.Protocol
import Game.ReceiptFreeness.ProtocolImplementation
import Game.IND-CCA2-dagger.ProtocolImplementation
import Game.Transformation.ReceiptFreeness-CCA2d.Protocol

open import Control.Protocol.CoreOld
open import Control.Protocol.BiSim
open import Control.Protocol.Reduction

open import Relation.Binary.PropositionalEquality.NP

module Game.Transformation.ReceiptFreeness-CCA2d.ProtocolImplementation
  (PubKey SecKey  : ★)
  (CipherText : ★)

  (SerialNumber : ★)
  --(Receipt : ★)
  --(MarkedReceipt? : ★)
  --(Ballot : ★)
  -- (Tally : ★)
  --(BB    : ★)
  --([]    : BB)
  --(_∷_ : Receipt → BB → BB)
  --(Rgb   : ★)
  -- (tallyMarkedReceipt? : let CO = 𝟚 in CO → MarkedReceipt? → Tally)
  -- (0,0   : Tally)
  -- (1,1   : Tally)
  -- (_+,+_ : Tally → Tally → Tally)
  (receipts : let open Receipt CipherText SerialNumber in SerialNumber ² → CipherText ² → Receipt ²)
  --(enc-co : Receipt → CipherText)
  --(m?     : Receipt → MarkedReceipt?)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ : ★)
  (#q : ℕ) (max#q : Fin #q)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → 𝟚 → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → 𝟚)
  (genBallot : let open Defs PubKey SecKey CipherText SerialNumber Rₑ Enc Dec
                   open Receipt CipherText SerialNumber
                in PubKey → Rgb → Ballot) -- this one should be abstract?
  (Check    : let open Defs PubKey SecKey CipherText SerialNumber Rₑ Enc Dec
                  open Receipt CipherText SerialNumber
               in BB → Receipt → 𝟚)
  -- (tally  : SecKey → BB → Tally)
  where

open Receipt CipherText SerialNumber
open Tally CipherText SerialNumber
open Defs PubKey SecKey CipherText SerialNumber Rₑ Enc Dec using (tally ; BB ; Rgb)

--_∷²_ : Receipt ² → BB → BB
-- r ∷² xs = r 0₂ ∷ (r 1₂ ∷ xs)


Message = 𝟚
-- CO = 𝟚
-- Candidate = 𝟚
EncReceipts : let CO = 𝟚 in
                 PubKey → Rₑ ² → SerialNumber ² → CO → Receipt ²
EncReceipts pk re sn co = receipts sn (λ x → Enc pk (x xor co) (re x))

DecReceipt : let CO = 𝟚 in
                SecKey → Receipt → CO
DecReceipt sk c = Dec sk (enc-co c)


open Game.ReceiptFreeness.Protocol PubKey (SerialNumber ²) Receipt Ballot BB Tally CO
open Explicit-definitions
open Game.IND-CCA2-dagger.Protocol PubKey Message CipherText

-- open Game.ReceiptFreeness.Protocol PubKey SerialNumber² Receipt Ballot BB Tally
open Game.IND-CCA2-dagger.ProtocolImplementation PubKey SecKey Message CipherText Rₑ Rₖ KeyGen Enc Dec

open Game.Transformation.ReceiptFreeness-CCA2d.Protocol PubKey CipherText (SerialNumber ²) Receipt MarkedReceipt? Ballot Tally BB [] _∷_ Rgb genBallot tallyMarkedReceipt? 0,0 1,1 _+,+_ receipts enc-co m? #q max#q Check

open Game.ReceiptFreeness.ProtocolImplementation PubKey SecKey (SerialNumber ²) (Rₑ ²) Rₖ #q max#q KeyGen Receipt EncReceipts DecReceipt Rgb Ballot BB [] _∷_ genBallot Tally tally Check hiding (_∷²_)

module proof (rgb : (Vec Rgb #q)²)(b : 𝟚)(rₖ : Rₖ)(rₑ : Rₑ ²) where

  pk = proj₁ (KeyGen rₖ)
  sk = proj₂ (KeyGen rₖ)

  postulate
 --   tally-naught : tally sk [] ≡ 0,0
    tally-both : ∀ sn bb
      → tally sk (EncReceipts pk rₑ sn b ∷² bb) ≡ (1,1 +,+ tally sk bb)

  {-
  each-phase : ∀ {X X'' p#}(bb : BB)(i : Fin #q)(C : _)(C' : _)(C'' : El 𝟙 X) →
           ServerSim Q Resp _
           (BiSim _≡_ {X})
           (Chal.service b pk sk rgb rₑ X p# C bb i)
           (applySim (service rgb pk p# C' bb i (tally sk bb))
                     (Challenger.service b pk sk rₑ C''))
  each-phase = {!!}
  -}

  phase2 : (bb : BB)(i : Fin #q) →
           ServerSim Q Resp _
           (BiSim _≡_ {end})
           (Chal.phase2 b pk sk rgb rₑ bb i)
           (applySim (sim-phase2 rgb pk bb i (tally sk bb))
                     (Challenger.phase2 b pk sk rₑ))
  phase2-vote : (bb : BB)(i : Fin #q)(x : _) →
    ServerResponseSim Q Resp 𝟙 _≡_
      (srv-ask (Chal.phase2 b pk sk rgb rₑ bb i) (Vote x))
      (applySimResp (service-vote rgb pk 1₂ (λ _ _ _ → end) bb i (tally sk bb) x (Check bb x))
                    (Challenger.phase2 b pk sk rₑ))

  sim-srv-ask (phase2 bb i) (Vote x) = phase2-vote bb i x -- (Check bb x) refl
  sim-srv-ask (phase2 bb i) REB = refl , phase2 bb (pred i)
  sim-srv-ask (phase2 bb i) RBB = refl , phase2 bb (pred i)
  sim-srv-ask (phase2 bb i) RTally = refl , phase2 bb (pred i)
  sim-srv-ask (phase2 bb i) (RCO x) = refl , (phase2 bb (pred i))
  sim-srv-done (phase2 bb i)   = refl

  phase2-vote bb i x with Check bb x
  ... | 0₂ = refl , phase2 bb (pred i)
  ... | 1₂ = refl , phase2 (x ∷ bb) (pred i) -- {!!} , {!!}

  exc : (bb : BB) → BiSim _≡_ {Exchange (Round end)}
        (Chal.exc b pk sk rgb rₑ bb)
        (apply (sim-chal rgb pk bb (tally sk bb))
               (Challenger.exchange b pk sk rₑ))
  exc bb sn with phase2 (EncReceipts pk rₑ sn b ∷² bb) max#q
  ... | con rewrite tally-both sn bb = refl , con

  phase1 : (bb : BB)(i : Fin #q) →
           ServerSim Q Resp _
           (BiSim _≡_ {Exchange (Round end)})
           (Chal.phase1 b pk sk rgb rₑ bb i)
           (applySim (sim-phase1 rgb pk bb i (tally sk bb))
                     (Challenger.phase1 b pk sk rₑ))
  phase1-vote : (bb : BB)(i : Fin #q)(x : _) →
    ServerResponseSim Q Resp (El 𝟙 (Exchange (Round end))) (BiSim _≡_ {Exchange (Round end)})
      (srv-ask (Chal.phase1 b pk sk rgb rₑ bb i) (Vote x))
      (applySimResp (service-vote rgb pk 0₂ (λ bb _ ta → sim-chal rgb pk bb ta) bb i (tally sk bb) x (Check bb x))
                    (Challenger.phase1 b pk sk rₑ))

  sim-srv-ask (phase1 bb i) (Vote x) = phase1-vote bb i x
  sim-srv-ask (phase1 bb i) REB = refl , phase1 bb (pred i)
  sim-srv-ask (phase1 bb i) RBB = refl , phase1 bb (pred i)
  sim-srv-ask (phase1 bb i) RTally = refl , phase1 bb (pred i)
  sim-srv-ask (phase1 bb i) (RCO x) = refl , phase1 bb (pred i)

  sim-srv-done (phase1 bb i) = exc bb

  phase1-vote bb i x with Check bb x
  ... | 0₂ = refl , phase1 bb (pred i)
  ... | 1₂ = refl , phase1 (x ∷ bb) (pred i)

  proof : BiSim _≡_ {P = ReceiptFreeness}(RF-C b rₖ rgb rₑ)
            (apply (simulator rgb) (CCA2d-Chal b rₖ rₑ))
  proof with phase1 [] max#q
  ... | con = refl , con -- rewrite tally-naught = refl , con

-- -}
-- -}
-- -}
-- -}
