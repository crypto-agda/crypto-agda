module forkable where

open import Level using (_⊔_)

record Forkable {s t} {S : Set s} (1+ : S → S) (_↝_ : S → S → Set t) : Set (s ⊔ t) where
  constructor mk
  field
    fork : ∀ {i o} (f g : i ↝ o) → (1+ i) ↝ o

open import Data.Product
open import Data.Bool

funFork : ∀ {s} → Forkable (_×_ Bool) (λ (A B : Set s) → A → B)
funFork {s} = mk fork where
  fork : ∀ {A B : Set s} → (f g : A → B) → Bool × A → B
  fork f g (b , x) = (if b then f else g) x

open import Data.Nat using (suc)
open import Data.Bits

bitsFunFork : Forkable suc (λ i o → Bits i → Bits o)
bitsFunFork = mk fork where
  fork : ∀ {i o} → (f g : Bits i → Bits o) → Bits (suc i) → Bits o
  fork f g (b ∷ x) = (if b then f else g) x
