{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Data.Two
open import Data.Maybe
open import Control.Protocol.CoreOld

module Game.IND-CCA2-dagger.Protocol
  (PubKey     : Type)
  (Message    : Type)
  (CipherText : Type)
  where

CCARound : Proto → Proto
CCARound = Server' CipherText (const (Maybe Message))

CCAChal : Proto → Proto
CCAChal X = Message ² →' (CipherText ² ×' X)

-- challenger implement this
CCA2-dagger : Proto
CCA2-dagger = PubKey ×' CCARound (CCAChal (CCARound end))
