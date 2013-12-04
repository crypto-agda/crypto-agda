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
open import Game.Challenge
import Game.ReceiptFreeness
import Game.IND-CCA2-dagger
import Game.IND-CPA-utils

import Data.List.Any
open Data.List.Any using (here; there)
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

module Game.Transformation.ReceiptFreeness-CCA2d.Valid
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


r-sn : Receipt → SerialNumber
r-sn (_ , sn , _) = sn

module Simulator-Valid (RFA : RF.Adversary)(RFA-Valid : RF.Valid-Adversary RFA)
  (WRONG-HYP : ∀ r r' → r-sn r ≡ r-sn r' → enc-co r ≡ enc-co r')
  where
  valid : CCA2†.Valid-Adversary (Simulator.A† RFA)
  valid (rₐ , rgb) pk = Phase1 _ (RFA-Valid rₐ pk) where
     open CCA2†.Valid-Adversary (rₐ , rgb) pk
     module RFA = RF.Valid-Adversary rₐ pk
     open Simulator RFA
     open AdversaryParts rgb pk rₐ

     -- could refine r more
     -- {-
     Phase2 : ∀ RF {bb i taA taB r} → r-sn (r 0₂) ∈ L.map r-sn bb → r-sn (r 1₂) ∈ L.map r-sn bb → RFA.Phase2-Valid r RF
            → Phase2-Valid (proj₂ ∘ proj₂ ∘ r) (mapS proj₁ (mitm-to-client-trans (MITM-phase 1₂ i bb (taA , taB)) RF))
     Phase2 (ask REB cont) r0 r1 RF-valid = Phase2 (cont _) r0 r1 (RF-valid _)
     Phase2 (ask RBB cont) r0 r1 RF-valid = Phase2 (cont _) r0 r1 (RF-valid _)
     Phase2 (ask RTally cont) r0 r1 RF-valid = Phase2 (cont _) r0 r1 (RF-valid _)
     Phase2 (ask (RCO x) cont) r0 r1 ((r₀ , r₁) , RF-valid) = r₀ , r₁ , (λ r → Phase2 (cont _) r0 r1 (RF-valid _))
     Phase2 (ask (Vote x) cont) {bb} r0 r1 RF-valid with Check bb x | CheckMem bb x
     ... | 0₂ | _ = Phase2 (cont _) r0 r1 (RF-valid _)
     ... | 1₂ | not-in-bb = (λ eq → not-in-bb _ {!subst (λ x → x ∈ L.map r-sn bb) eq!})
                            , {!!},
                            , λ r → Phase2 (cont _) (there r0) (there r1) (RF-valid _)
     Phase2 (done x) r0 r1 RF-valid = RF-valid

     Phase1 : ∀ RF {sn i bb taA taB} → RFA.Phase1-Valid sn RF
            → Phase1-Valid (mapS A†2 (mitm-to-client-trans (MITM-phase 0₂ i bb (taA , taB)) RF))
     Phase1 (ask REB cont) RF-valid = Phase1 _ (RF-valid _)
     Phase1 (ask RBB cont) RF-valid = Phase1 _ (RF-valid _)
     Phase1 (ask RTally cont) RF-valid = Phase1 _ (RF-valid _)
     Phase1 (ask (RCO x) cont) RF-valid r = Phase1 _ (RF-valid _)
     Phase1 (ask (Vote x) cont) {bb = bb} RF-valid with Check bb x
     Phase1 (ask (Vote x) cont) RF-valid | 1₂ = λ r → Phase1 _ (RF-valid _)
     Phase1 (ask (Vote x) cont) RF-valid | 0₂ = Phase1 _ (RF-valid _)
     Phase1 (done x) (sn₀∉sn , sn₁∉sn , RF-valid) cs = Phase2 (put-resp x (proj₂ (put-resp (hack-challenge x) cs) ))
            (here refl) (there (here refl)) (RF-valid _)
    -- -}

-- -}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
