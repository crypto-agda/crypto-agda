open import Function
open import Data.Nat.NP
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≗_; _≡_)

open import Data.Bits
import flipbased

module flipbased-counting
   (↺ : ∀ {a} → ℕ → Set a → Set a)
   (toss : ↺ 1 Bit)
   (return↺ : ∀ {n a} {A : Set a} → A → ↺ n A)
   (map↺ : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → ↺ n A → ↺ n B)
   (join↺ : ∀ {n₁ n₂ a} {A : Set a} → ↺ n₁ (↺ n₂ A) → ↺ (n₁ + n₂) A)
   (count↺ : ∀ {n} → ↺ n Bit → ℕ)
 where

open flipbased ↺ toss return↺ map↺ join↺

infix 4 _≈↺_ _≋↺_ _≈⅁?_

-- f ≈↺ g when f and g return the same number of 1 (and 0).
_≈↺_ : ∀ {n} (f g : EXP n) → Set
_≈↺_ = _≡_ on count↺

_≈⅁?_ : ∀ {c} (g₀ g₁ : ⅁? c) → Set
g₀ ≈⅁? g₁ = ∀ b → g₀ b ≈↺ g₁ b

_∼[_]EXP_ : ∀ {m n} → EXP m → (ℕ → ℕ → Set) → EXP n → Set
_∼[_]EXP_ {m} {n} f _∼_ g = ⟨2^ n * count↺ f ⟩ ∼ ⟨2^ m * count↺ g ⟩

_≋↺_ : ∀ {m n} → EXP m → EXP n → Set
f ≋↺ g = f ∼[ _≡_ ]EXP g

Safe⅁? : ∀ {c} (f : ⅁? c) → Set
Safe⅁? f = f 0b ≈↺ f 1b

Reversible⅁? : ∀ {c} (g : ⅁? c) → Set
Reversible⅁? g = g ≈⅁? g ∘ not

≈⇒≋↺ : ∀ {n} {f g : EXP n} → f ≈↺ g → f ≋↺ g
≈⇒≋↺ eq rewrite eq = ≡.refl

≋⇒≈↺ : ∀ {n} {f g : EXP n} → f ≋↺ g → f ≈↺ g
≋⇒≈↺ {n} = 2^-inj n

module ≈⅁? {n} where
  setoid : Setoid _ _
  setoid = record { Carrier = C; _≈_ = ℛ; isEquivalence = isEquivalence }
      where
        C : Set _
        C = ⅁? n

        ℛ : C → C → Set _
        ℛ = _≈⅁?_

        refl : Reflexive ℛ
        refl b = ≡.refl

        sym : Symmetric ℛ
        sym p b = ≡.sym (p b)

        trans : Transitive ℛ
        trans p q b = ≡.trans (p b) (q b)

        isEquivalence : IsEquivalence ℛ
        isEquivalence = record { refl = λ {x} → refl {x}
                               ; sym = λ {x y} → sym {x} {y}
                               ; trans = λ {x y z} → trans {x} {y} {z} }

  module Reasoning = Setoid-Reasoning setoid 
  open Setoid setoid public

module ≋↺ {n} where
  setoid : Setoid _ _
  setoid = record { Carrier = C; _≈_ = ℛ; isEquivalence = isEquivalence }
      where
        C : Set _
        C = EXP n

        ℛ : C → C → Set _
        ℛ = _≋↺_

        refl : Reflexive ℛ
        refl = ≡.refl

        sym : Symmetric ℛ
        sym = ≡.sym

        trans : Transitive ℛ
        trans = ≡.trans

        isEquivalence : IsEquivalence ℛ
        isEquivalence = record { refl = λ {x} → refl {x}
                               ; sym = λ {x y} → sym {x} {y}
                               ; trans = λ {x y z} → trans {x} {y} {z} }

  module Reasoning = Setoid-Reasoning setoid 
  open Setoid setoid public

module ≈↺ {n} where
  setoid : Setoid _ _
  setoid = record { Carrier = C; _≈_ = ℛ; isEquivalence = isEquivalence }
      where
        C : Set _
        C = EXP n

        ℛ : C → C → Set _
        ℛ = _≈↺_

        refl : Reflexive ℛ
        refl = ≡.refl

        sym : Symmetric ℛ
        sym = ≡.sym

        trans : Transitive ℛ
        trans = ≡.trans

        isEquivalence : IsEquivalence ℛ
        isEquivalence = record { refl = λ {x} → refl {x}
                               ; sym = λ {x y} → sym {x} {y}
                               ; trans = λ {x y z} → trans {x} {y} {z} }

  module Reasoning = Setoid-Reasoning setoid 
  open Setoid setoid public

module ⅁? {n} where
  join : EXP n → EXP n → ⅁? n
  join f g b = if b then f else g

  safe-sym : ∀ {g : ⅁? n} → Safe⅁? g → Safe⅁? (g ∘ not)
  safe-sym {g} g-safe = ≈↺.sym {n} {g 0b} {g 1b} g-safe

  Reversible⇒Safe : ∀ {c} (g : ⅁? c) → Reversible⅁? g → Safe⅁? g
  Reversible⇒Safe g g≈g∘not = g≈g∘not 0b

data Rat : Set where _/_ : (num denom : ℕ) → Rat

Pr[_≡1] : ∀ {n} (f : EXP n) → Rat
Pr[_≡1] {n} f = count↺ f / 2^ n
