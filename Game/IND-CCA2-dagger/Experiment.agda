{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Control.Strategy renaming (run to run-round)

open import Crypto.Schemes
open import Game.Challenge
import Game.IND-CPA-utils
import Game.IND-CCA2-dagger.Adversary
import Game.IND-CCA2-dagger.Valid

module Game.IND-CCA2-dagger.Experiment
  (pke : Pubkey-encryption)
  (Rₐ : Type)
  where

open Pubkey-encryption pke

open Game.IND-CCA2-dagger.Adversary PubKey Message CipherText Rₐ public

R : ★
R = Rₐ × Rₖ × Rₑ × Rₑ

Experiment : ★
Experiment = Adversary → R → 𝟚

module EXP (b : 𝟚) (A : Adversary) (rₐ : Rₐ) (pk : PubKey) (sk : SecKey) (rₑ : Rₑ ²) where
  A1       = A rₐ pk
  cpaA     = run-round (dec sk) A1
  m        = get-chal cpaA
  c        = enc pk ∘ m ∘ flip _xor_ b ˢ rₑ
  A2       = put-resp cpaA c
  b'       = run-round (dec sk) A2

  c₀ = c 0₂
  c₁ = c 1₂
  rₑ₀ = rₑ 0₂
  rₑ₁ = rₑ 1₂

  c₀-spec : c₀ ≡ enc pk (m b) rₑ₀
  c₀-spec = refl

  c₁-spec : c₁ ≡ enc pk (m (not b)) rₑ₁
  c₁-spec = refl

EXP : 𝟚 → Experiment
EXP b A (rₐ , rₖ , rₑ₀ , rₑ₁) with key-gen rₖ
... | pk , sk = EXP.b' b A rₐ pk sk [0: rₑ₀ 1: rₑ₁ ]
