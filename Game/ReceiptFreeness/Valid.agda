{-# OPTIONS --without-K #-}
open import Type
open import Data.One using (𝟙)
open import Data.List as L
open import Data.Product
open import Data.Two
open import Game.Challenge
open import Control.Strategy
open import Relation.Binary.PropositionalEquality

import Data.List.Any
open Data.List.Any.Membership-≡ using (_∉_)
import Game.ReceiptFreeness.Adversary

module Game.ReceiptFreeness.Valid
  (PubKey SerialNumber Rₐ Receipt Ballot Tally CO BB : ★)
  (CipherText : ★)
  (enc-co : Receipt → CipherText)
  (r-sn   : Receipt → SerialNumber)
  (b-sn   : Ballot → SerialNumber)
  where

open Game.ReceiptFreeness.Adversary PubKey (SerialNumber ²) Rₐ Receipt Ballot Tally CO BB

module Valid-Adversary (rₐ : Rₐ)(pk : PubKey) where

  module _ (rec : Receipt ²) where
    RCO-ok : Receipt → ★
    RCO-ok r = enc-co (rec 0₂) ≢ enc-co r
             × enc-co (rec 1₂) ≢  enc-co r

    Phase2-Valid : Phase 𝟚 → ★
    Phase2-Valid (ask REB cont) = ∀ r → Phase2-Valid (cont r)
    Phase2-Valid (ask RBB cont) = ∀ r → Phase2-Valid (cont r)
    Phase2-Valid (ask RTally cont) = ∀ r → Phase2-Valid (cont r)
    Phase2-Valid (ask (RCO x) cont) = RCO-ok x × (∀ r → Phase2-Valid (cont r))
    Phase2-Valid (ask (Vote x) cont) = ∀ r → Phase2-Valid (cont r)
    Phase2-Valid (done x)      = 𝟙

  RFChallenge-Valid : List SerialNumber → RFChallenge (Phase 𝟚) → ★
  RFChallenge-Valid sn ch = sn₀ ∉ sn × sn₁ ∉ sn × (∀ r → Phase2-Valid r (put-resp ch r))
    where sn₀ = get-chal ch 0₂
          sn₁ = get-chal ch 1₂

  serials : ∀ q → Resp q → List SerialNumber
  serials REB X = L.[ b-sn X ]
  serials RBB r = []
  serials RTally r = []
  serials (RCO v) r = L.[ r-sn v ] -- page 75
  serials (Vote v) r = L.[ r-sn v ] -- page 75

  Phase1-Valid : List SerialNumber → Phase (RFChallenge (Phase 𝟚)) → ★
  Phase1-Valid sn (ask q? cont) = ∀ r → Phase1-Valid (serials q? r L.++ sn) (cont r)
  Phase1-Valid sn (done x) = RFChallenge-Valid sn x

  Valid : Adversary → ★
  Valid A = Phase1-Valid [] (A rₐ pk)

Valid-Adversary : Adversary → ★
Valid-Adversary A = ∀ rₐ pk → Valid-Adversary.Valid rₐ pk A
