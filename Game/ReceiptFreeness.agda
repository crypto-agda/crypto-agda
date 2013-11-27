open import Function using (_∘_)
open import Type using (★)
open import Data.Fin.NP using (Fin)
import Data.List as L
open import Data.Nat.NP using (ℕ)
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Two using (𝟚 ; ✓)
import Data.List.Any as LA

import Relation.Binary.PropositionalEquality.NP as ≡

private
  open module DUMMY {X : ★} = LA.Membership (≡.setoid X) 

-- module that re-exports the important definitions for the ReceiptFreeness game
module Game.ReceiptFreeness
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
 -- (Check : CipherText → 𝟚)
 -- (CheckEnc : ∀ pk m rₑ → Check (Enc pk m rₑ) ≡ 1₂)

  where

open import Game.ReceiptFreeness.Definitions PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec public
open import Game.ReceiptFreeness.Valid PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec public

module WithCheck
  (Check    : BB → Receipt → 𝟚)
  (CheckMem : ∀ bb r → ✓ (Check bb r) → proj₁ (proj₂ r) ∉ L.map (proj₁ ∘ proj₂) bb) where
  open import Game.ReceiptFreeness.Experiment PubKey SecKey CipherText SerialNumber Rₑ Rₖ Rₐ #q max#q KeyGen Enc Dec
                                              Check CheckMem public
