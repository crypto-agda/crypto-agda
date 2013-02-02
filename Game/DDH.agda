open import Type
open import Data.Bits
open import Data.Product

-- Decisional Diffe-Hellman security game
module Game.DDH
  (ℤq  : ★)
  (_⊠_ : ℤq → ℤq → ℤq)
  (G   : ★)
  (g^_ : ℤq → G)
  (Rₐ  : ★) where

-- Decisional Diffe-Hellman smoothing adversary
Adv : ★
Adv = Rₐ → G → G → G → Bit

-- The randomness supply needed for the decisional
-- Diffe-Hellman games
R : ★
R = Rₐ × ℤq × ℤq × ℤq

-- Decisional Diffe-Hellman game:
--   * input: adversary and randomness supply
--   * output b: adversary claims we are in game ⅁ b
Game : ★
Game = Adv → R → Bit

-- The adversary is given correlated inputs
⅁₀ : Game
⅁₀ d (r , x , y , _) = d r (g^ x) (g^ y) (g^ (x ⊠ y))

-- The adversary is given independent inputs
⅁₁ : Game
⅁₁ d (r , x , y , z) = d r (g^ x) (g^ y) (g^ z)

-- Package ⅁₀ and ⅁₁
⅁ : Bit → Game
⅁ = proj (⅁₀ , ⅁₁)
