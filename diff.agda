module diff where

open import Data.Nat.NP
open import Relation.Binary.PropositionalEquality

diff : ℕ → ℕ → ℕ
diff zero y = y
diff x zero = x
diff (suc x) (suc y) = diff x y

{-
postulate
  diff-refl  : ∀ x → diff x x ≡ 0
  diff-sym   : ∀ x y → diff x y ≡ diff y x
  diff-sum   : ∀ x y z → diff x y + diff y z ≤ diff x z
  diff-≤     : ∀ x y → diff x y ≤ x
  diff-x+    : ∀ x y z → diff (x + y) (x + z) ≡ diff y z
  diff-mono₁ : ∀ x y z t → x ≤ y → diff z t ≤ diff (x + z) (y + t)
  diff-x*  : ∀ x y z → diff (x * y) (x * z) ≡ x * diff y z
-}

-- Haskell
-- let diff x y = abs (x - y)
-- quickCheck (forAll (replicateM 3 (choose (0,100))) (\ [x,y,z] -> diff (x * y) (x * z) == x * diff y z))
