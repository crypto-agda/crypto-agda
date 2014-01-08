
{-# OPTIONS --without-K #-}
open import Function
open import Type
open import Data.Product renaming (zip to zip-×)
open import Data.Two
open import Data.List as L
open import Data.Nat.NP hiding (_==_)
import Game.ReceiptFreeness.Definitions.Receipt

module Game.ReceiptFreeness.Definitions.Tally
  (CipherText : ★)

  (SerialNumber : ★)
  where

open Game.ReceiptFreeness.Definitions.Receipt CipherText SerialNumber

Tally : ★
Tally = ℕ × ℕ

alice-score : Tally → ℕ
alice-score = proj₁

bob-score : Tally → ℕ
bob-score = proj₂

1:alice-0:bob 0:alice-1:bob : Tally
1:alice-0:bob = 1 , 0
0:alice-1:bob = 0 , 1

data TallyMarkedReceipt-spec : CO → MarkedReceipt → Tally → ★ where
  c1 : TallyMarkedReceipt-spec alice-then-bob marked-on-first-cell  1:alice-0:bob
  c2 : TallyMarkedReceipt-spec alice-then-bob marked-on-second-cell 0:alice-1:bob
  c3 : TallyMarkedReceipt-spec bob-then-alice marked-on-first-cell  0:alice-1:bob
  c4 : TallyMarkedReceipt-spec bob-then-alice marked-on-second-cell 1:alice-0:bob

marked-for-alice? : CO → MarkedReceipt → 𝟚
marked-for-alice? co m = co == m

marked-for-bob? : CO → MarkedReceipt → 𝟚
marked-for-bob? co m = not (marked-for-alice? co m)

tallyMarkedReceipt : CO → MarkedReceipt → Tally
tallyMarkedReceipt co m = 𝟚▹ℕ for-alice , 𝟚▹ℕ (not for-alice)
  where for-alice = marked-for-alice? co m

tallyMarkedReceipt-ok : ∀ co m → TallyMarkedReceipt-spec co m (tallyMarkedReceipt co m)
tallyMarkedReceipt-ok 1₂ 1₂ = c4
tallyMarkedReceipt-ok 1₂ 0₂ = c3
tallyMarkedReceipt-ok 0₂ 1₂ = c2
tallyMarkedReceipt-ok 0₂ 0₂ = c1

tallyMarkedReceipt? : CO → MarkedReceipt? → Tally
tallyMarkedReceipt? co not-marked    = 0 , 0
tallyMarkedReceipt? co (marked mark) = tallyMarkedReceipt co mark

_+,+_ : Tally → Tally → Tally
_+,+_ = zip-× _+_ _+_

-- Not taking advantage of any homomorphic encryption
tallyClearBB : ClearBB → Tally
tallyClearBB = L.foldr _+,+_ (0 , 0) ∘ L.map (uncurry tallyMarkedReceipt?)

0,0 : Tally
0,0 = 0 , 0

1,1 : Tally
1,1 = 1 , 1
