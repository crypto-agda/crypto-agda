{-# OPTIONS --without-K #-}
module Composition.Forkable where

open import Type  hiding (★)
open import Level using (_⊔_)

record Forkable {s t} {S : ★ s}
                (1+ : S → S)
                (_↝_ : S → S → ★ t) : ★ (s ⊔ t) where
  constructor mk
  field
    fork : ∀ {i o} (f g : i ↝ o) → (1+ i) ↝ o

open import Data.Product
open import Data.Bool

funFork : ∀ {s} → Forkable (_×_ Bool) (λ (A B : ★ s) → A → B)
funFork {s} = mk fork where
  fork : ∀ {A B : ★ s} → (f g : A → B) → Bool × A → B
  fork f g (b , x) = (if b then f else g) x

open import Data.Nat using (suc)
open import Data.Bits

bitsFunFork : Forkable suc _→ᵇ_
bitsFunFork = mk fork where
  fork : ∀ {i o} → (f g : i →ᵇ o) → suc i →ᵇ o
  fork f g (b ∷ x) = (if b then f else g) x
