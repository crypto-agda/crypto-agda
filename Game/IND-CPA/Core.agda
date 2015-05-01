{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Function
open import Data.Product.NP
open import Data.Zero
open import Data.One
open import Data.Two
open import Game.Generic as GenChal
open import Control.Protocol.CoreOld
open import Relation.Binary.PropositionalEquality

module Game.IND-CPA.Core
  (PubKey     : Type)
  (SecKey     : Type)
  (Message    : Type)
  (CipherText : Type)

  -- randomness supply for: encryption, key-generation, adversary, extensions
  (Rₑ Rₖ Rₐ Rₓ : Type)

  (key-gen : Rₖ → PubKey × SecKey)
  (enc     : PubKey → Message → Rₑ → CipherText)
  where

challenge : PubKey → 𝟚 → Message ² → Rₑ → CipherText
challenge pk b m rₑ = enc pk (m b) rₑ

-- Using the generic protocol
module CPA-Proto = GenChal PubKey (const 𝟘) (λ()) (Message ²)  CipherText 𝟚
module CPA-challenger = CPA-Proto.Challenger-implementation 𝟙 𝟚 (λ _ ()) challenge

-- IND-CPA adversary in two parts
record Adversary : Type where
  constructor _,_
  field
    -- In the step 'm', the adversary receives some randomness,
    -- the public key, the message we want (m₀ or m₁). The adversary
    -- returns the message to encrypt. Remember that the adversary
    -- is a pure and deterministic function, therefore 𝟚 → Message
    -- is the same as Message × Message.
    m  : Rₐ → PubKey → 𝟚 → Message

    -- In the step 'b′' the adversary receives the same randomness
    -- supply and public key as in step 'm' and receives the ciphertext
    -- computed by the challenger. The adversary has to guess which
    -- message (m₀, m₁) has been encrypted.
    b′ : Rₐ → PubKey → CipherText → 𝟚

Adversaryᴳ : Type
Adversaryᴳ = Rₐ → El 𝟙 CPA-Proto.Adversary-proto.Main

Adversary→Adversaryᴳ : Adversary → Adversaryᴳ
Adversary→Adversaryᴳ A rₐ pk = done (A.m rₐ pk , (λ c → done (A.b′ rₐ pk c , _)))
  where module A = Adversary A

Adversaryᴳ→Adversary : Adversaryᴳ → Adversary
Adversary.m  (Adversaryᴳ→Adversary Aᴳ) rₐ pk   = fst (un-client0 (Aᴳ rₐ pk))
Adversary.b′ (Adversaryᴳ→Adversary Aᴳ) rₐ pk c = fst (un-client0 (snd (un-client0 (Aᴳ rₐ pk)) c))

-- IND-CPA randomness supply
R : Type
R = (Rₐ × Rₖ × Rₑ × Rₓ)

-- IND-CPA experiments:
--   * input: adversary and randomness supply
--   * output b′: adversary claims we are in experiment EXP b
Experiment : Type
Experiment = Adversary → R → 𝟚

-- The game step by step:
-- (pk) key-generation, only the public-key is needed
-- (mb) send randomness, public-key and bit
--      receive which message to encrypt
-- (c)  encrypt the message
-- (b′) send randomness, public-key and ciphertext
--      receive the guess from the adversary
EXP : 𝟚 → Experiment
EXP b A (rₐ , rₖ , rₑ , _rₓ) = res
  where
  module A = Adversary A
  pk  = fst (key-gen rₖ)
  mb  = A.m rₐ pk b
  c   = enc pk mb rₑ
  res = A.b′ rₐ pk c

EXP₀ EXP₁ : Experiment
EXP₀ = EXP 0₂
EXP₁ = EXP 1₂

game : Adversary → (𝟚 × R) → 𝟚
game A (b , r) = b == EXP b A r

-- Generic
module _ where
    Experimentᴳ : Type
    Experimentᴳ = Adversaryᴳ → R → 𝟚

    EXPᴳ : 𝟚 → Experimentᴳ
    EXPᴳ b A (rₐ , rₖ , rₑ , _rₓ) = CPA-challenger.main-com b pk _ rₑ (A rₐ)
      where
        pk  = fst (key-gen rₖ)

    EXP≡EXPᴳ : EXP ≡ (λ b → EXPᴳ b ∘ Adversary→Adversaryᴳ)
    EXP≡EXPᴳ = refl

    gameᴳ : Adversaryᴳ → (𝟚 × R) → 𝟚
    gameᴳ Aᴳ (b , r) = b == EXPᴳ b Aᴳ r

    game≡gameᴳ : game ≡ gameᴳ ∘ Adversary→Adversaryᴳ
    game≡gameᴳ = refl

module _
  (Dist : Type)
  (|Pr[_≡1]-Pr[_≡1]| : (f g : R → 𝟚) → Dist)
  (dist-comm : ∀ f g → |Pr[ f ≡1]-Pr[ g ≡1]| ≡ |Pr[ g ≡1]-Pr[ f ≡1]|)
  where

    Advantage : Adversary → Dist
    Advantage A = |Pr[ EXP₀ A ≡1]-Pr[ EXP₁ A ≡1]|

    Advantage-unordered : ∀ A b → Advantage A ≡ |Pr[ EXP b A ≡1]-Pr[ EXP (not b) A ≡1]|
    Advantage-unordered A 1₂ = dist-comm _ _
    Advantage-unordered A 0₂ = refl
