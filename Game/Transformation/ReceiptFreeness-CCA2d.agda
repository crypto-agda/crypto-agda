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

import Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst
import Game.Transformation.ReceiptFreeness-CCA2d.Proof

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
  (Check    : let open Game.ReceiptFreeness PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec
               in BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → proj₁ (proj₂ r) ∉ L.map (proj₁ ∘ proj₂) bb)
  -- (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)
  where

open Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen
         Enc Dec Check public hiding (module CCA2†)

open Game.Transformation.ReceiptFreeness-CCA2d.Proof PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen
         Enc Dec Check CheckMem public


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
