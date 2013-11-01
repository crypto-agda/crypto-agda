
{-# OPTIONS --without-K #-}
open import Type
open import Data.Product
open import Data.Bit

module Game.IND-CPA-dagger
  (PubKey     : ★)
  (SecKey     : ★)
  (Message    : ★)
  (CipherText : ★)

  -- randomness supply for: encryption, key-generation, adversary, extensions
  (Rₑ Rₖ Rₐ Rₓ : ★)

  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)

where

-- In the step 0, the adversary receives some randomness,
-- the public key, the message we want (m₀, m₁). The adversary
-- returns the message to encrypt. Remember that the adversary
-- is a pure and deterministic function, therefore Bit → Message
-- is the same as Message × Message.
AdvStep₀ : ★
AdvStep₀ = Rₐ → PubKey → Bit → Message

-- In the step 1 the adversary receives the same randomness
-- supply and public key as in step 0 and receives the ciphertext
-- computed by the challenger. The adversary has to guess which
-- message (m₀, m₁) has been encrypted.
AdvStep₁ : ★
AdvStep₁ = Rₐ → PubKey → CipherText → CipherText → Bit

-- IND-CPA adversary in two parts
Adv : ★
Adv = AdvStep₀ × AdvStep₁

-- IND-CPA randomness supply
R : ★
R = (Rₐ × Rₖ × Rₑ × Rₑ × Rₓ)

-- IND-CPA games:
--   * input: adversary and randomness supply
--   * output b: adversary claims we are in game ⅁ b
Game : ★
Game = Adv → R → Bit

-- The game step by step:
-- (pk) key-generation, only the public-key is needed
-- (mb) send randomness, public-key and bit
--      receive which message to encrypt
-- (c)  encrypt the message
-- (b′) send randomness, public-key and ciphertext
--      receive the guess from the adversary
⅁ : Bit → Game
⅁ b (m , d) (rₐ , rₖ , rₑ , rₑ′ , _rₓ) = b′
  where
  pk = proj₁ (KeyGen rₖ)
  mb = m rₐ pk
  c  = Enc pk (mb b)       rₑ
  c′ = Enc pk (mb (not b)) rₑ′
  b′ = d rₐ pk c c′

⅁₀ ⅁₁ : Game
⅁₀ = ⅁ 0b
⅁₁ = ⅁ 1b
