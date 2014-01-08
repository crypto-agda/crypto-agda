{-# OPTIONS --copatterns #-}

open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Maybe
open import Data.Product

open import Data.Nat.NP
--open import Rat

open import Explore.Core
open import Explore.Explorable
open import Explore.Product
open Operators
open import Control.Strategy renaming (run to runStrategy)
open import Control.Protocol.Core
open import Game.Challenge
import Game.IND-CPA-utils

import Game.IND-CCA2-dagger.Adversary
import Game.IND-CCA2-dagger.Valid
import Game.IND-CCA2-dagger.Experiment

open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2-dagger.Protocol
  (PubKey    : ★)
  (Message   : ★)
  (CipherText : ★)
  where


CCARound : Proto → Proto
CCARound = Server' CipherText (const Message)

CCAChal : Proto → Proto
CCAChal X = Message ² →' (CipherText ² ×' X)

-- challenger implement this
CCA2-dagger : Proto
CCA2-dagger = PubKey ×'
              CCARound (CCAChal (CCARound end))

