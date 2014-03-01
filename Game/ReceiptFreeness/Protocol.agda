{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Function
open import Data.Two

open import Control.Protocol.CoreOld

module Game.ReceiptFreeness.Protocol
  (PubKey SerialNumber² Receipt Ballot BB Tally CO : ★)
  where

data Accept? : ★ where
  accept reject : Accept?

data Q : ★ where
  REB RBB RTally : Q
  RCO            : Receipt → Q
  Vote           : Receipt → Q

Resp : Q → ★
Resp REB = Ballot
Resp (RCO x) = CO
Resp (Vote x) = Accept?
Resp RBB = BB
Resp RTally = Tally

module Explicit-definitions where
  Round : Proto → Proto
  Round Next = Server' Q Resp Next

  Exchange : Proto → Proto
  Exchange Next = SerialNumber² →' (Receipt ² ×' Next)

  ReceiptFreeness : Proto
  ReceiptFreeness =  PubKey
                  ×' Round (Exchange (Round end))

module Derived-from-IND-CCA2-gen where -- TODO remove
  open import Game.IND-CCA2-gen.Protocol PubKey Q Resp (Receipt ²) SerialNumber²

{-
module Derived-from-GenChal where -- TODO switch to this one
  open import Game.Generic PubKey (const Q) Resp (Receipt ²) SerialNumber² end
-}

-- -}
-- -}
-- -}
-- -}
-- -}
