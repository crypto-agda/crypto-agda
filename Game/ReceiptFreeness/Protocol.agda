{-# OPTIONS --copatterns #-}
open import Type
open import Data.Two

open import Control.Protocol.Core
import Game.IND-CCA2-gen.Protocol

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

open Game.IND-CCA2-gen.Protocol PubKey Q Resp (Receipt ²) SerialNumber²

module Manual where
  Round : Proto → Proto
  Round Next = Server' Q Resp Next

  Exchange : Proto → Proto
  Exchange Next = SerialNumber² →' (Receipt ² ×' Next)

  ReceiptFreeness : Proto
  ReceiptFreeness = PubKey
                 ×' Round (Exchange (Round end))

-- -}
-- -}
-- -}
-- -}
-- -}
