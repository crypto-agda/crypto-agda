{-# OPTIONS --copatterns #-}
open import Type
open import Data.Fin
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Two
open import Data.Vec using (Vec ; lookup)

import Game.ReceiptFreeness.Adversary
import Game.ReceiptFreeness.Protocol
import Game.IND-CCA2-dagger.Protocol

import Game.ReceiptFreeness.Definitions.Receipt as Receipt

open import Control.Protocol.CoreOld
open import Control.Protocol.Reduction

module Game.Transformation.ReceiptFreeness-CCA2d.Protocol
  (PubKey    : ★)
  (CipherText : ★)

  (SerialNumber² : ★)
  -- (open Receipt CipherText SerialNumber²)
  (Receipt : ★)
  (MarkedReceipt? : ★)
  (Ballot : ★)
  (Tally : ★)
  (BB    : ★)
  ([]    : BB)
  (_∷_ : Receipt → BB → BB)
  (Rgb   : ★)
  (genBallot : PubKey → Rgb → Ballot)
  (tallyMarkedReceipt? : let CO = 𝟚 in CO → MarkedReceipt? → Tally)
  (0,0   : Tally)
  (1,1   : Tally)
  (_+,+_ : Tally → Tally → Tally)
  (receipts : SerialNumber² → CipherText ² → Receipt ²)
  (enc-co : Receipt → CipherText)
  (m?     : Receipt → MarkedReceipt?)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (#q : ℕ) (max#q : Fin #q)
  (Check    : BB → Receipt → 𝟚)
  where

_∷²_ : Receipt ² → BB → BB
r ∷² xs = r 0₂ ∷ (r 1₂ ∷ xs)

Message = 𝟚
CO = 𝟚
Candidate = 𝟚

open Game.ReceiptFreeness.Protocol PubKey SerialNumber² Receipt Ballot BB Tally CO
open Explicit-definitions

open Game.IND-CCA2-dagger.Protocol PubKey Message CipherText

module _ (rgb : (Vec Rgb #q)²)(pk : PubKey) where
  ballot : 𝟚 → Fin #q → Ballot
  ballot p# n = genBallot pk (lookup n (rgb p#))

  module _ {A B : Proto}(p# : 𝟚)(cont : BB → Fin #q → Tally → A ⊢ B) where
    service : BB → Fin #q → Tally → RServerSim (CCARound A) Q Resp B
    service-vote : BB → Fin #q → Tally → (x : Receipt) → 𝟚
                 → CCARound A ⊢[ Q , Resp , Vote x ] B

    r-ask (service bb i ta) REB = ret (ballot p# i , service bb (pred i) ta)
    r-ask (service bb i ta) RBB = ret (bb , service bb (pred i) ta)
    r-ask (service bb i ta) RTally = ret (ta , service bb (pred i) ta)
    r-ask (service bb i ta) (RCO r) = LS-ask (enc-co r , λ co →
      ret (co , (service bb (pred i) ta)))
    r-ask (service bb i ta) (Vote x) = service-vote bb i ta x (Check bb x)
    r-done (service bb i ta)  = LS-done (cont bb i ta)

    service-vote bb i ta v 0₂ = ret (reject , (service bb (pred i) ta))
    service-vote bb i ta v 1₂ = LS-ask (enc-co v , (λ co →
      ret (accept , service (v ∷ bb) (pred i) (tallyMarkedReceipt? co (m? v) +,+ ta))))

  sim-phase2 : BB → Fin #q → Tally → RServerSim (CCARound end) Q Resp end
  sim-phase2 = service 1₂ (λ _ _ _ → end)

  sim-chal : BB → Tally → (Message ² →' (CipherText ² ×' CCARound end))
           ⊢ (SerialNumber² →' (Receipt ² ×' Round end))
  sim-chal bb ta = RΠ (λ sn → LΠ ((λ x → x) , LΣ (λ c →
     let r = receipts sn c
      in RΣ (r , RS (sim-phase2 (r ∷² bb) max#q (1,1 +,+ ta))))))

  sim-phase1 : BB → Fin #q → Tally
             → RServerSim (CCARound (Message ² →' (CipherText ² ×' CCARound end)))
               Q Resp (SerialNumber² →' (Receipt ² ×' Round end))
  sim-phase1 = service 0₂ (λ bb _ ta → sim-chal bb ta)

simulator : (Vec Rgb #q)² → CCA2-dagger ⊢ ReceiptFreeness
simulator r = LΣ (λ pk → RΣ (pk , RS (sim-phase1 r pk [] max#q 0,0)))


-- -}
-- -}
-- -}
-- -}
