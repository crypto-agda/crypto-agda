{-# OPTIONS --without-K #-}
open import Function
open import Data.Nat.NP
open import Data.Fin using (Fin)
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≗_; _≡_)

open import Data.Bits
open import Data.Bits.Count
import flipbased
import flipbased-counting

module flipbased-running
   (↺ : ∀ {a} → ℕ → Set a → Set a)
   (toss : ↺ 1 Bit)
   (return↺ : ∀ {n a} {A : Set a} → A → ↺ n A)
   (map↺ : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → ↺ n A → ↺ n B)
   (join↺ : ∀ {n₁ n₂ a} {A : Set a} → ↺ n₁ (↺ n₂ A) → ↺ (n₁ + n₂) A)
   (run↺ : ∀ {n a} {A : Set a} → ↺ n A → Bits n → A)
 where

open flipbased ↺ toss return↺ map↺ join↺

count↺ᶠ : ∀ {c} → EXP c → Fin (suc (2^ c))
count↺ᶠ f = #⟨ run↺ f ⟩ᶠ

count↺ : ∀ {c} → EXP c → ℕ
count↺ f = #⟨ run↺ f ⟩

open flipbased-counting ↺ toss return↺ map↺ join↺ count↺

infix 4 _≗↺_ _≗⅁?_

_≗↺_ : ∀ {c a} {A : Set a} (f g : ↺ c A) → Set a
f ≗↺ g = run↺ f ≗ run↺ g

_≗⅁?_ : ∀ {c} (g₀ g₁ : ⅁? c) → Set
g₀ ≗⅁? g₁ = ∀ b → g₀ b ≗↺ g₁ b

Reversible-≗⅁? : ∀ {c} (g : ⅁? c) → Set
Reversible-≗⅁? g = g ≗⅁? g ∘ not

≗⇒≈↺ : ∀ {c} {f g : EXP c} → f ≗↺ g → f ≈↺ g
≗⇒≈↺ {f = f} {g} = ≗-cong-# (run↺ f) (run↺ g)

≗⇒≋↺ : ∀ {c} {f g : EXP c} → f ≗↺ g → f ≋↺ g
≗⇒≋↺ eq rewrite ≗⇒≈↺ eq = ≡.refl


difference-lemma↺ : ∀ {n}(A B F : EXP n)
  → #⟨ |not| (run↺ F) |∧| run↺ A ⟩ ≡ #⟨ |not| (run↺ F) |∧| run↺ B ⟩
  → dist #⟨ run↺ A ⟩ #⟨ run↺ B ⟩ ≤ #⟨ run↺ F ⟩
difference-lemma↺ A B F = difference-lemma (run↺ A) (run↺ B) (run↺ F)



module ≗↺ {n} {a} {A : Set a} where
  setoid : Setoid _ _
  setoid = record { Carrier = C; _≈_ = ℛ; isEquivalence = isEquivalence }
      where
        C : Set _
        C = ↺ n A

        ℛ : C → C → Set _
        ℛ = _≗↺_

        refl : Reflexive ℛ
        refl _ = ≡.refl

        sym : Symmetric ℛ
        sym p x = ≡.sym (p x)

        trans : Transitive ℛ
        trans p q x = ≡.trans (p x) (q x)

        isEquivalence : IsEquivalence ℛ
        isEquivalence = record { refl = refl; sym = sym; trans = trans }

  module Reasoning = Setoid-Reasoning setoid 
  open Setoid setoid public

module ≗⅁? {n} where
  setoid : Setoid _ _
  setoid = record { Carrier = C; _≈_ = ℛ; isEquivalence = isEquivalence }
      where
        C : Set _
        C = ⅁? n

        ℛ : C → C → Set _
        ℛ = _≗⅁?_

        refl : Reflexive ℛ
        refl _ _ = ≡.refl

        sym : Symmetric ℛ
        sym p b R = ≡.sym (p b R)

        trans : Transitive ℛ
        trans p q b R = ≡.trans (p b R) (q b R)

        isEquivalence : IsEquivalence ℛ
        isEquivalence = record { refl = refl; sym = sym; trans = trans }

  module Reasoning = Setoid-Reasoning setoid 
  open Setoid setoid public

≋↺-cong-≗↺ : ∀ {c c'} {f g : EXP c} {f' g' : EXP c'} → f ≗↺ g → f' ≗↺ g' → f ≋↺ f' → g ≋↺ g'
≋↺-cong-≗↺ f≗g f'≗g' f≈f' rewrite ≗⇒≈↺ f≗g | ≗⇒≈↺ f'≗g' = f≈f'

≈↺-cong-≗↺ : ∀ {n} {f g f' g' : EXP n} → f ≗↺ g → f' ≗↺ g' → f ≈↺ f' → g ≈↺ g'
≈↺-cong-≗↺ f≗g f'≗g' f≈f' rewrite ≗⇒≈↺ f≗g | ≗⇒≈↺ f'≗g' = f≈f'

Reversible-≗⅁?⇒Reversible⅁? : ∀ {c} (g : ⅁? c) → Reversible-≗⅁? g → Reversible⅁? g
Reversible-≗⅁?⇒Reversible⅁? g g≈g∘not = ≗⇒≈↺ ∘ g≈g∘not
