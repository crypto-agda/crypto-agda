{-# OPTIONS --without-K #-}
-- This is an alternative version of
-- ZK.JSChecker.verify-PoK-CP-EG-rnd
-- which we could instantiate with a JS instance of 𝕊.
open import Crypto.Syntax
open import ZK.Types using (PoK-CP-EG-rnd; module PoK-CP-EG-rnd)

module ZK.Checker {U}(T : 𝕋 U)([_] : U → Set)(S : 𝕊 T [_]) where

open 𝕋 T
open 𝕊 S
open Types T [_]

verify-PoK-CP-EG-rnd : (pok : PoK-CP-EG-rnd [ ℤq ] [ ℤp★ ]) → [ Bool ]
verify-PoK-CP-EG-rnd pok = gˢ==αᶜ·A ∧ yˢ==⟨β/M⟩ᶜ·B
  module verify-PoK-CP-EG-rnd where
    open module pok = PoK-CP-EG-rnd pok
    open ℤp★-Eq?
    M = g ^ m
    gˢ==αᶜ·A     = g ^ s == (α ^ c) ** A
    yˢ==⟨β/M⟩ᶜ·B = y ^ s == ((β // M) ^ c) ** B
