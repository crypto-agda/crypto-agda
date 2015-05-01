{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Control.Strategy

open import Game.Challenge
import Game.IND-CPA-utils
import Game.IND-CCA2-dagger.Adversary

module Game.IND-CCA2-dagger.Valid
  (PubKey     : Type)
  (Message    : Type)
  (CipherText : Type)
  (Rₐ         : Type)
  where

open Game.IND-CPA-utils Message CipherText

open Game.IND-CCA2-dagger.Adversary PubKey Message CipherText Rₐ

module Valid-Adversary (rₐ : Rₐ)(pk : PubKey) where

  module _ (rec : CipherText ²) where
    Phase2-Valid : DecRound 𝟚 → Type
    Phase2-Valid (ask q? cont) = rec 0₂ ≢ q? × rec 1₂ ≢ q? × (∀ r → Phase2-Valid (cont r))
    Phase2-Valid (done x) = 𝟙

  Chal-Valid : ChalAdversary (Message ²) (CipherText ²) (DecRound 𝟚) → Type
  Chal-Valid A = ∀ cs →  Phase2-Valid cs (put-resp A cs)

  Phase1-Valid : DecRound (ChalAdversary (Message ²) (CipherText ²) (DecRound 𝟚)) → Type
  Phase1-Valid (ask q? cont) = ∀ r → Phase1-Valid (cont r)
  Phase1-Valid (done A) = Chal-Valid A

  Valid : Adversary → Type
  Valid A = Phase1-Valid (A rₐ pk)

Valid-Adversary : Adversary → Set
Valid-Adversary A = ∀ rₐ pk → Valid-Adversary.Valid rₐ pk A
