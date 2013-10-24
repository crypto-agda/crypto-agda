{-# OPTIONS --without-K #-}
open import FunUniverse.Core
open import Data.Nat.NP
open import Data.Bits
module FunUniverse.Interface.Bits
         {t} {T : Set t} (funU : FunUniverse T) where
open FunUniverse funU

record FunBits : Set t where
  field
    <0∷_> : ∀ {n A} → (A `→ `Bits n) → A `→ `Bits (1 + n)

    <1∷_> : ∀ {n A} → (A `→ `Bits n) → A `→ `Bits (1 + n)

    constBits : ∀ {n _⊤} → Bits n → _⊤ `→ `Bits n

    <0ⁿ> : ∀ {n _⊤} → _⊤ `→ `Bits n

    <1ⁿ> : ∀ {n _⊤} → _⊤ `→ `Bits n

    constBits′′ : ∀ {n _⊤} → Bits n → _⊤ `→ `Bits n

    exploreBits : ∀ {n A} → (A `× A `→ A) → (`Bits n `→ A) → `𝟙 `→ A

    {-
    findBits? : ∀ {n A} → (`Bits n `→? A) → `𝟙 `→? A

    findBits𝟚 : ∀ {n} → (`Bits n `→ `Bit) → `𝟙 `→? `Bits n

    fromTree : ∀ {n A} → Tree (`𝟙 `→ A) n → `Bits n `→ A
    -}

    fromFun : ∀ {n A} → (Bits n → `𝟙 `→ A) → `Bits n `→ A

    fromBitsFun : ∀ {i o} → (i →ᵇ o) → i `→ᵇ o

    <==> : ∀ {n} → `Bits n `× `Bits n `→ `Bit

    <⊕> : ∀ {n} → `Bits n `× `Bits n `→ `Bits n

    --vnot : ∀ {n} → `Endo (`Bits n)

    --sucBCarry : ∀ {n} → `Bits n `→ `Bits (1 + n)

    --sucB : ∀ {n} → `Bits n `→ `Bits n
