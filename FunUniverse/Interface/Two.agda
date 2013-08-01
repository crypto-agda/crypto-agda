{-# OPTIONS --without-K #-}
open import FunUniverse.Core
open import Data.Two
module FunUniverse.Interface.Two
         {t} {T : Set t} (funU : FunUniverse T) where
open FunUniverse funU

record FunTwo : Set t where

  field
    -- already part of a record
    <0₂> <1₁> : ∀ {_𝟙} → _𝟙 `→ `𝟚

    <not> : `𝟚 `→ `𝟚

    const𝟚 : ∀ {_𝟙} → 𝟚 → _𝟙 `→ `𝟚

    <0,_> : ∀ {A B} → (A `→ B) → A `→ `𝟚 `× B

    <1,_> : ∀ {A B} → (A `→ B) → A `→ `𝟚 `× B

    <0,> : ∀ {A} → A `→ `𝟚 `× A

    <1,> : ∀ {A} → A `→ `𝟚 `× A

    <0,1> : ∀ {_𝟙} → _𝟙 `→ `𝟚 `× `𝟚

    <xor> : `𝟚 `× `𝟚 `→ `𝟚

    <or> : `𝟚 `× `𝟚 `→ `𝟚

    <and> : `𝟚 `× `𝟚 `→ `𝟚

    <==ᵇ> : `𝟚 `× `𝟚 `→ `𝟚

    half-adder : `𝟚 `× `𝟚 `→ `𝟚 `× `𝟚

    full-adder : `𝟚 `× `𝟚 `× `𝟚 `→ `𝟚 `× `𝟚
