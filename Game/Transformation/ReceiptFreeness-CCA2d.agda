open import Type
open import Function
open import Data.Two
open import Data.Maybe
open import Data.Product
open import Data.Nat
open import Data.Fin using (Fin)
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

  record ServerResp {Q : ★₀} (q : Q) (R : Q → ★₀) (A : ★₀) : ★₀ where
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
    data MITM : ★ where
        mk : ((q' : Q') → Σ Q λ q → R q → R' q' × MITM) → MITM

    hacked-com : Server Q R A → MITM → Client Q' R' A' → A'
    hacked-com srv (mk mitm) (ask q κc) =
      case mitm q of λ { (q , mitm2) →
      case srv q of λ r →
      case mitm2 (srv-resp r) of λ { (r' , mitm3) →
         hacked-com (srv-cont r) mitm3 (κc r')
      } }
    hacked-com srv mitm (done x) = x

Message = 𝟚
open Game.IND-CPA-utils Message CipherText
module RF    = Game.ReceiptFreeness PubKey SecKey         CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec Check CheckEnc
module CCA2† = Game.IND-CCA2-dagger PubKey SecKey Message CipherText              Rₑ Rₖ Rₐ          KeyGen Enc Dec
open RF using (RFChallenge; Candidate) renaming (Phase to RFPhase; Q to RFQ; Resp to RFResp)

module _  (RFA : RF.Adversary) where

  A : CCA2†.Adversary
  A rₐ pk = foo
    where
      bar : _ → _ -- RFChallenge (RFPhase Candidate) → DecRound (CPAAdversary (DecRound {!!}))
      bar rfc = {!!}
      p : RFPhase ≡ Strategy RFQ RFResp
      p = refl
      foo : DecRound (CPAAdversary (CipherText → DecRound Candidate))
      foo = mapS {RFChallenge (RFPhase Candidate)} {CPAAdversary (CipherText → DecRound Candidate)} {RFQ} {CipherText} {!!} {!!}
               {!RFA rₐ pk!}


-- -}
-- -}
-- -}
-- -}
-- -}
