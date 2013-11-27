open import Type
open import Data.Fin.NP using (Fin)
open import Data.Nat.NP using (ℕ)
open import Data.One using (𝟙)
open import Data.List as L
open import Data.Product
open import Data.Two
open import Game.Challenge
open import Control.Strategy
open import Relation.Binary.PropositionalEquality

import Data.List.Any as LA
open module MM {X : ★} = LA.Membership (setoid X)

module Game.ReceiptFreeness.Valid
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
  where

open import Game.ReceiptFreeness.Definitions PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec


module Valid-Adversary (rₐ : Rₐ)(pk : PubKey) where

  module _ (rec : Receipt ²) where
    RCO-ok : Receipt → ★
    RCO-ok (m? , sn , c) = proj₂ (proj₂ (rec 0₂)) ≢ c
                         × proj₂ (proj₂ (rec 1₂)) ≢ c

  
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
  serials REB (_ , _ , sn , _) = L.[ sn ]
  serials RBB r = []
  serials RTally r = []
  serials (RCO (_ , sn , _)) r = L.[ sn ] -- page 75
  serials (Vote (_ , sn , _)) r = L.[ sn ] -- page 75

  Phase1-Valid : List SerialNumber → Phase (RFChallenge (Phase 𝟚)) → ★
  Phase1-Valid sn (ask q? cont) = ∀ r → Phase1-Valid (serials q? r L.++ sn) (cont r)
  Phase1-Valid sn (done x) = RFChallenge-Valid sn x

  Valid : Adversary → ★
  Valid A = Phase1-Valid [] (A rₐ pk)

-- TODO adversary validity
Valid-Adversary : Adversary → ★
Valid-Adversary A = ∀ rₐ pk → Valid-Adversary.Valid rₐ pk A
