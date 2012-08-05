module flipbased-gen where

import Level as L
open import Function
open import Data.Bits
open import Data.Nat.NP
open import Data.Vec
open import Data.Unit using (⊤)
open import Data.Product
open import Relation.Binary.NP
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as ≡
import Data.Fin as Fin
open ≡ using (_≗_; _≡_)
open Fin using (Fin; suc)

import flipbased
import flipbased-counting
import flipbased-running

-- “↺ n A” reads like: “toss n coins and then return a value of type A”
record ↺ {a r} (R : Set r) (A : Set a) : Set (r L.⊔ a) where
  constructor mk
  field
    run↺ : R → A

open ↺ public

private
  -- If you are not allowed to toss any coin, then you are deterministic.
  Det : ∀ {a} → Set a → Set a
  Det = ↺ ⊤

runDet : ∀ {a} {A : Set a} → Det A → A
runDet f = run↺ f _

randomTODO : ∀ {a} {A : Set a} → ↺ A A
randomTODO = mk id

toss : ↺ Bit Bit
toss = randomTODO

return↺ : ∀ {r a} {R : Set r} {A : Set a} → A → ↺ R A
return↺ = mk ∘ const

map↺ : ∀ {r a b} {R : Set r} {A : Set a} {B : Set b}
       → (A → B) → ↺ R A → ↺ R B
map↺ f x = mk (f ∘ run↺ x)
-- map↺ f x ≗ x >>=′ (return {0} ∘ f)

join↺ : ∀ {r₁ r₂ a} {R₁ : Set r₁} {R₂ : Set r₂} {A : Set a}
        → ↺ R₁ (↺ R₂ A) → ↺ (R₁ × R₂) A
join↺ x = mk (λ { (π₁ , π₂) → run↺ (run↺ x π₁) π₂ })
-- join↺ x = x >>= id

comap : ∀ {r₁ r₂ a} {R₁ : Set r₁} {R₂ : Set r₂} {A : Set a}
        → (R₂ → R₁) → ↺ R₁ A → ↺ R₂ A
comap f (mk g) = mk (g ∘ f)

{-
open flipbased ↺ toss return↺ map↺ join↺ public
open flipbased-running ↺ toss return↺ map↺ join↺ run↺ public
open flipbased-counting ↺ toss return↺ map↺ join↺ count↺ public
-}
