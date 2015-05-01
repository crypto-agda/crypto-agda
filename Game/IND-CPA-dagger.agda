{-# OPTIONS --without-K #-}
open import Type
open import Data.Product.NP
open import Data.Two

open import Crypto.Schemes

module Game.IND-CPA-dagger
  (pke : Pubkey-encryption)
  -- randomness supply for: adversary, extensions
  (Rₐ Rₓ : Type)
  where

open Pubkey-encryption pke

-- IND-CPA† adversary in two parts
record Adversary : Type where
  field
    -- Same as in IND-CPA:
    -- In the step 'm', the adversary receives some randomness,
    -- the public key, the message we want (m₀ or m₁). The adversary
    -- returns the message to encrypt. Remember that the adversary
    -- is a pure and deterministic function, therefore 𝟚 → Message
    -- is the same as Message × Message.
    m  : Rₐ → PubKey → 𝟚 → Message

    -- In the step 'b′' the adversary receives the same randomness
    -- supply and public key as in step 'm' and receives two ciphertexts
    -- computed by the challenger. One of the ciphertext should be
    -- the encryption of m₀ and the other of m₁.
    -- The adversary has to guess in which order they are, namely
    -- is the first ciphertext the encryption of m₀.
    b' : Rₐ → PubKey → CipherText → CipherText → 𝟚

-- IND-CPA randomness supply
R : Type
R = (Rₐ × Rₖ × Rₑ × Rₑ × Rₓ)

-- IND-CPA experiments:
--   * input: adversary and randomness supply
--   * output b: adversary claims we are in experiment EXP b
Experiment : Type
Experiment = Adversary → R → 𝟚

-- The game step by step:
-- (pk) key-generation, only the public-key is needed
-- (mb) send randomness, public-key and bit
--      receive which message to encrypt
-- (c)  encrypt the message
-- (b′) send randomness, public-key and ciphertext
--      receive the guess from the adversary
EXP : (b t : 𝟚) → Experiment
EXP b t A (rₐ , rₖ , rₑ , rₑ' , _rₓ) = b'
  where
  module A = Adversary A
  pk = fst (key-gen rₖ)
  mb = A.m rₐ pk
  c  = enc pk (mb b) rₑ
  c' = enc pk (mb t) rₑ'
  b' = A.b' rₐ pk c c'

EXP₀ EXP₁ : Experiment
EXP₀ = EXP 0₂ 1₂
EXP₁ = EXP 1₂ 0₂

game : Adversary → (𝟚 × R) → 𝟚
game A (b , r) = b == EXP b (not b) A r

open import Relation.Binary.PropositionalEquality
module _
  (Dist : Type)
  (|Pr[_≡1]-Pr[_≡1]| : (f g : R → 𝟚) → Dist)
  (dist-comm : ∀ f g → |Pr[ f ≡1]-Pr[ g ≡1]| ≡ |Pr[ g ≡1]-Pr[ f ≡1]|)
  where

    Advantage : Adversary → Dist
    Advantage A = |Pr[ EXP₀ A ≡1]-Pr[ EXP₁ A ≡1]|

    Advantage-unordered : ∀ A b → Advantage A ≡ |Pr[ EXP b (not b) A ≡1]-Pr[ EXP (not b) b A ≡1]|
    Advantage-unordered A 1₂ = dist-comm _ _
    Advantage-unordered A 0₂ = refl
-- -}
-- -}
-- -}
