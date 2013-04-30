open import Type
open import Data.Two
open import Data.Product

-- Decisional Diffie-Hellman security game
module Game.DDH
  (ℤq G : ★)
  (g    : G)
  (_^_  : G → ℤq → G)
  (Rₐ   : ★)
  where

-- The type of DDH adversaries:
Adv : ★
Adv = Rₐ → G → G → G → 𝟚

-- The randomness supply needed for DDH games
R : ★
R = Rₐ × ℤq × ℤq × ℤq

-- Decisional Diffie-Hellman game:
--   * input: adversary and randomness supply
--   * output b: adversary claims we are in game ⅁ b
Game : ★
Game = Adv → R → 𝟚

-- The adversary is given correlated inputs
⅁₀ : Game
⅁₀ d (r , x , y , _) = d r (g ^ x) (g ^ y) ((g ^ x) ^ y)

-- The adversary is given independent inputs
⅁₁ : Game
⅁₁ d (r , x , y , z) = d r (g ^ x) (g ^ y) (g ^ z)

-- Package ⅁₀ and ⅁₁
⅁ : 𝟚 → Game
⅁ = proj (⅁₀ , ⅁₁)
