{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Function
open import Data.Two
open import Data.Maybe
open import Data.Product.NP
open import Data.Nat
open import Data.List as L
open import Data.Fin as Fin using (Fin)
open import Relation.Binary.PropositionalEquality.NP as ≡
import Game.ReceiptFreeness

import Data.List.Any
open Data.List.Any.Membership-≡ using (_∈_ ; _∉_)

open import Crypto.Schemes
import Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst
import Game.Transformation.ReceiptFreeness-CCA2d.Proof

module Game.Transformation.ReceiptFreeness-CCA2d
  (pke : Pubkey-encryption)
  (open Pubkey-encryption pke)
  (SerialNumber : Type)
  (Rₐ : Type)
  (𝟚→Message : 𝟚 → Message)
  (Message→𝟚 : Maybe Message → 𝟚)
  (𝟚→Message→𝟚 : ∀ m → Message→𝟚 (just (𝟚→Message m)) ≡ m)
  (#q : ℕ) (max#q : Fin #q)

  (open Game.ReceiptFreeness pke SerialNumber Rₑ 𝟚→Message Message→𝟚 #q max#q)
  (Check    : BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → fst (snd r) ∉ L.map (fst ∘ snd) bb)
  -- (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)
  where

open Game.Transformation.ReceiptFreeness-CCA2d.SimulatorInst pke SerialNumber Rₐ 𝟚→Message Message→𝟚 #q max#q Check
         public hiding (module CCA2†)

open Game.Transformation.ReceiptFreeness-CCA2d.Proof pke SerialNumber Rₐ 𝟚→Message Message→𝟚 𝟚→Message→𝟚 #q max#q Check CheckMem
         public


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
