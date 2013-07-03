open import FunUniverse.Core
module FunUniverse.Interface.Two
         {t} {T : Set t} (funU : FunUniverse T) where
open FunUniverse funU

record FunTwo where

  field
    -- already part of a record
    <0b> <1b> : ∀ {_⊤} → _⊤ `→ `Bit

    not : `Bit `→ `Bit

    constBit : ∀ {_⊤} → Bit → _⊤ `→ `Bit

    <0,_> : ∀ {A B} → (A `→ B) → A `→ `Bit `× B

    <1,_> : ∀ {A B} → (A `→ B) → A `→ `Bit `× B

    <0,> : ∀ {A} → A `→ `Bit `× A

    <1,> : ∀ {A} → A `→ `Bit `× A

    <0,1> : ∀ {_⊤} → _⊤ `→ `Bit `× `Bit

    <xor> : `Bit `× `Bit `→ `Bit

    <or> : `Bit `× `Bit `→ `Bit

    <and> : `Bit `× `Bit `→ `Bit

    <==ᵇ> : `Bit `× `Bit `→ `Bit

    half-adder : `Bit `× `Bit `→ `Bit `× `Bit

    full-adder : `Bit `× `Bit `× `Bit `→ `Bit `× `Bit
