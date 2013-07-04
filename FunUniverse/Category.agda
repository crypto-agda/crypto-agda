open import Level.NP using (_⊔_)
open import Type hiding (★)
open import Function.NP using (Endo)
open import Data.Nat using (ℕ; zero; suc)

module FunUniverse.Category
  {t ℓ} {T : ★ t}
  (_`→_ : T → T → ★ ℓ)
  where

module CompositionNotations
  (_∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C))
  {A B C} where

  infixr 1 _⁏_
  infixr 1 _>>>_

  _⁏_ : (A `→ B) → (B `→ C) → (A `→ C)
  f ⁏ g = g ∘ f

  _<<<_ : (B `→ C) → (A `→ B) → (A `→ C)
  g <<< f = g ∘ f

  _>>>_ : (A `→ B) → (B `→ C) → (A `→ C)
  f >>> g = f ⁏ g

record Category : ★ (ℓ ⊔ t) where
  constructor _,_

  infixr 9 _∘_
  field
    id : ∀ {A} → A `→ A
    _∘_ : ∀ {A B C} → (B `→ C) → (A `→ B) → (A `→ C)

  private
    `Endo : T → Set ℓ
    `Endo A = A `→ A

  iterate : ∀ {A} → ℕ → Endo (`Endo A)
  iterate zero    _ = id
  iterate (suc n) f = iterate n f ∘ f
