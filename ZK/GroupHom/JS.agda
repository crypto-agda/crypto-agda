{-# OPTIONS --without-K #-}
open import FFI.JS.BigI
open import SynGrp

module ZK.GroupHom.JS
  (qChal : BigI)
  {`𝔾+ `𝔾* : SynGrp}
  (`φ : SynHom `𝔾+ `𝔾*)
  (`Y : ElGrp `𝔾*)
  where

open import ZK.GroupHom.JSChal
  qChal _ _
  {{SynGrp-Eq? `𝔾*}}
  (expI `𝔾+) (expI `𝔾*)
  (ElHom `φ) (Elℍom `φ)
  `Y public
-- -}
