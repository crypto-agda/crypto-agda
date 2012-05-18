module composable where

open import Level
open import Function
open import Data.Unit using (⊤)

-- Monoid M ≅ Cat (ConstArr M)

Composition : ∀ {i a} {I : Set i} (_↝_ : I → I → Set a) → Set (i ⊔ a)
Composition _↝_ = ∀ {A B C} → (A ↝ B) → (B ↝ C) → (A ↝ C)

record IComposable {i j s t} {I : Set i} {_↝ᵢ_ : I → I → Set j} {S : I → Set s}
                   (_·_ : Composition _↝ᵢ_)
                   (⟨_⟩_↝_ : ∀ {i₀ i₁} → i₀ ↝ᵢ i₁ → S i₀ → S i₁ → Set t) : Set (t ⊔ s ⊔ i ⊔ j) where
  constructor mk
  infixr 1 _>>>_
  field
    _>>>_ : ∀ {i₀ i₁ i₂} {ix₀ : i₀ ↝ᵢ i₁} {ix₁ : i₁ ↝ᵢ i₂} {A B C}
            → (⟨ ix₀ ⟩ A ↝ B) → (⟨ ix₁ ⟩ B ↝ C) → (⟨ ix₀ · ix₁ ⟩ A ↝ C)

open import Data.Unit using (⊤)

ConstArr : ∀ {a} (A : Set a) → ⊤ → ⊤ → Set a
ConstArr A _ _ = A

Composable : ∀ {s t} {S : Set s} (_↝_ : S → S → Set t) → Set (s ⊔ t)
Composable _↝_ = IComposable {i = zero} {_↝ᵢ_ = ConstArr ⊤} _ (const _↝_)

{- Composable, unfolded:
record Composable {s t} {S : Set s} (_↝_ : S → S → Set t) : Set (s ⊔ t) where
  constructor mk
  infixr 1 _>>>_
  field
    _>>>_ : ∀ {A B C : S} → (A ↝ B) → (B ↝ C) → (A ↝ C)
-}

constComp' : ∀ {a} {A : Set a} (_·_ : A → A → A) → Composition (ConstArr A)
constComp' _·_ = _·_

constComp : ∀ {a} {A : Set a} (_·_ : A → A → A) → Composable (ConstArr A)
constComp _·_ = mk _·_

module Composable = IComposable

ixFunComp : ∀ {ix s} {Ix : Set ix} (F : Ix → Set s) → Composable (λ i o → F i → F o)
ixFunComp _ = mk (λ f g x → g (f x))

funComp : ∀ {s} → Composable (λ (A B : Set s) → A → B)
funComp = ixFunComp id

opComp : ∀ {s t} {S : Set s} {_↝_ : S → S → Set t} → Composable _↝_ → Composable (flip _↝_)
opComp (mk _>>>_) = mk (flip _>>>_)

open import Data.Vec
vecFunComp : ∀ {a} (A : Set a) → Composable (λ i o → Vec A i → Vec A o)
vecFunComp A = ixFunComp (Vec A)

open import Data.Bits
bitsFunComp : Composable (λ i o → Bits i → Bits o)
bitsFunComp = ixFunComp Bits

-- open import Data.Fin
-- funRewireComp : Composable (λ i o → Fin o → Fin i)
-- FunRewireComp = opComp (ixFunComp Fin)

{-
open import bintree

open import Data.Nat
CircuitType : Set₁
CircuitType = (i o : ℕ) → Set

RewireTbl : CircuitType
RewireTbl i o = Vec (Fin i) o

rewireTblComp : Composable RewireTbl
rewireTblComp = {!!}
-}
