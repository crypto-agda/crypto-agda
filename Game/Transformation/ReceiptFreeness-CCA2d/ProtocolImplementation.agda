
{-# OPTIONS --copatterns #-}
open import Type
open import Data.Fin
open import Data.Nat using (ℕ)
open import Data.Nat.Properties.Simple
open import Data.One
open import Data.Product
open import Data.Two
open import Data.Vec using (Vec ; lookup)
open import Data.List using ([] ; _∷_)


open import Function using (flip)

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

open import Algebra.FunctionProperties {A = ℕ × ℕ} _≡_

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
  -- (receipts : let open Receipt CipherText SerialNumber in SerialNumber ² → CipherText ² → Receipt ²)
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
  (DecEnc : ∀ rₖ rₑ m → let pk , sk = KeyGen rₖ in Dec sk (Enc pk m rₑ) ≡ m)
  -- (tally  : SecKey → BB → Tally)
  where

open Receipt CipherText SerialNumber
open Tally CipherText SerialNumber
module DEFS = Defs PubKey SecKey CipherText SerialNumber Rₑ Enc Dec
open DEFS using (tally ; BB ; Rgb)

--_∷²_ : Receipt ² → BB → BB
-- r ∷² xs = r 0₂ ∷ (r 1₂ ∷ xs)


-- Doesn't matter which mark it is, we arbitrary pick 1₂
receipts : SerialNumber ² → CipherText ² → Receipt ²
receipts sn cs b = marked 1₂ , sn b , cs b

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

+,+-assoc : Associative _+,+_
+,+-assoc x y z = ap₂ _,_ (+-assoc (proj₁ x) (proj₁ y) (proj₁ z))
                          (+-assoc (proj₂ x) (proj₂ y) (proj₂ z))

module proof (rgb : (Vec Rgb #q)²)(b : 𝟚)(rₖ : Rₖ)(rₑ : Rₑ ²) where

  pk = proj₁ (KeyGen rₖ)
  sk = proj₂ (KeyGen rₖ)

 -- postulate
 --   tally-naught : tally sk [] ≡ 0,0
  tally-both : ∀ sn bb
      → tally sk (EncReceipts pk rₑ sn b ∷² bb) ≡ (1,1 +,+ tally sk bb)
  tally-both sn bb = ! +,+-assoc a0 a1 (tally sk bb) ∙ ap (flip _+,+_ (tally sk bb)) lemma
    where
      a0 = uncurry tallyMarkedReceipt? (DEFS.DecReceipt sk (EncReceipts pk rₑ sn b 0₂))
      a1 = uncurry tallyMarkedReceipt? (DEFS.DecReceipt sk (EncReceipts pk rₑ sn b 1₂))

      lemma : a0 +,+ a1 ≡ 1,1
      lemma rewrite DecEnc rₖ (rₑ 0₂) b
                  | DecEnc rₖ (rₑ 1₂) (not b)
              with not b
      ... | 0₂ = refl
      ... | 1₂ = refl

  module _ {X X'}(p# : 𝟚)(ChalNext : BB → El 𝟙 X)(ChallengerNext : El 𝟙 X')(SimNext : BB → Fin #q → Tally → X' ⊢ X)
    (BiSimNext : ∀ bb i → BiSim _≡_ {X} (ChalNext bb) (apply (SimNext bb i (tally sk bb)) ChallengerNext)) where
    mutual
      service-phase : (bb : BB)(i : Fin #q) →
               ServerSim Q Resp _
               (BiSim _≡_ {X})
               (Chal.service b pk sk rgb rₑ X p# ChalNext bb i)
               (applySim (service rgb pk p# SimNext bb i (tally sk bb))
                         (Challenger.service b pk sk rₑ {X'} ChallengerNext))
      sim-srv-ask (service-phase bb i) (Vote x) = service-phase-vote bb i x -- (Check bb x) refl
      sim-srv-ask (service-phase bb i) REB = refl , service-phase bb (pred i)
      sim-srv-ask (service-phase bb i) RBB = refl , service-phase bb (pred i)
      sim-srv-ask (service-phase bb i) RTally = refl , service-phase bb (pred i)
      sim-srv-ask (service-phase bb i) (RCO x) = refl , (service-phase bb (pred i))
      sim-srv-done (service-phase bb i)   = BiSimNext bb i

      service-phase-vote : (bb : BB)(i : Fin #q)(x : _) →
        ServerResponseSim Q Resp (El 𝟙 X) (BiSim _≡_ {X})
          (srv-ask (Chal.service b pk sk rgb rₑ X p# ChalNext bb i) (Vote x))
          (applySimResp (service-vote rgb pk p# SimNext bb i (tally sk bb) x (Check bb x))
                        (Challenger.service b pk sk rₑ {X'} ChallengerNext))
      service-phase-vote bb i x with Check bb x
      ... | 0₂ = refl , service-phase bb (pred i) -- service-phase bb (pred i)
      ... | 1₂ = refl , service-phase (x ∷ bb) (pred i) -- service-phase (x ∷ bb) (pred i) -- {!!} , {!!}


  phase2 : (bb : BB)(i : Fin #q) →
           ServerSim Q Resp _
           (BiSim _≡_ {end})
           (Chal.phase2 b pk sk rgb rₑ bb i)
           (applySim (sim-phase2 rgb pk bb i (tally sk bb))
                     (Challenger.phase2 b pk sk rₑ))
  phase2 = service-phase 1₂ _ _ _ (λ _ _ → refl)

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
  phase1 = service-phase 0₂ _ _ _ (λ bb _ sn → exc bb sn)

  proof : BiSim _≡_ {P = ReceiptFreeness}(RF-C b rₖ rgb rₑ)
            (apply (simulator rgb) (CCA2d-Chal b rₖ rₑ))
  proof with phase1 [] max#q
  ... | con = refl , con -- rewrite tally-naught = refl , con

-- -}
-- -}
-- -}
-- -}
