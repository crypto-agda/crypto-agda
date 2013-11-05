{-# OPTIONS --without-K #-}
open import Type
open import Data.Product
open import Data.Two

module Game.IND-CPA
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
-- is a pure and deterministic function, therefore 𝟚 → Message
-- is the same as Message × Message.
AdvStep₀ : ★
AdvStep₀ = Rₐ → PubKey → 𝟚 → Message

-- In the step 1 the adversary receives the same randomness
-- supply and public key as in step 0 and receives the ciphertext
-- computed by the challenger. The adversary has to guess which
-- message (m₀, m₁) has been encrypted.
AdvStep₁ : ★
AdvStep₁ = Rₐ → PubKey → CipherText → 𝟚

-- IND-CPA adversary in two parts
Adversary : ★
Adversary = AdvStep₀ × AdvStep₁

-- IND-CPA randomness supply
R : ★
R = (Rₐ × Rₖ × Rₑ × Rₓ)

-- IND-CPA experiments:
--   * input: adversary and randomness supply
--   * output b′: adversary claims we are in experiment EXP b
Experiment : ★
Experiment = Adversary → R → 𝟚

-- The game step by step:
-- (pk) key-generation, only the public-key is needed
-- (mb) send randomness, public-key and bit
--      receive which message to encrypt
-- (c)  encrypt the message
-- (b′) send randomness, public-key and ciphertext
--      receive the guess from the adversary
EXP : 𝟚 → Experiment
EXP b (m , b′) (rₐ , rₖ , rₑ , _rₓ) = res
  where
  pk  = proj₁ (KeyGen rₖ)
  mb  = m rₐ pk b
  c   = Enc pk mb rₑ
  res = b′ rₐ pk c

EXP₀ EXP₁ : Experiment
EXP₀ = EXP 0₂
EXP₁ = EXP 1₂

game : Adversary → (𝟚 × R) → 𝟚
game A (b , r) = b == EXP b A r

open import Relation.Binary.PropositionalEquality
module _
  (Dist : ★)
  (|Pr[_≡1]-Pr[_≡1]| : (f g : R → 𝟚) → Dist)
  (dist-comm : ∀ f g → |Pr[ f ≡1]-Pr[ g ≡1]| ≡ |Pr[ g ≡1]-Pr[ f ≡1]|)
  where

    Advantage : Adversary → Dist
    Advantage A = |Pr[ EXP₀ A ≡1]-Pr[ EXP₁ A ≡1]|

    Advantage-unordered : ∀ A b → Advantage A ≡ |Pr[ EXP b A ≡1]-Pr[ EXP (not b) A ≡1]|
    Advantage-unordered A 1₂ = dist-comm _ _
    Advantage-unordered A 0₂ = refl
