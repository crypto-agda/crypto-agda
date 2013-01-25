open import Type hiding (★)
open import Function.NP
open import Data.Product
open import Search.Type
open import Search.Searchable

module Search.Searchable.Product where

private
    Cont : ∀ {a m} → ★ m → ★ a → ★ _
    Cont M A = (A → M) → M

    ΣF : ∀ {a b m} {A : ★ a} {B : A → ★ b} {M : ★ m}
         → Cont M A → (∀ {x} → Cont M (B x)) → Cont M (Σ A B)
    ΣF fA fB f = fA (fB ∘ curry f)

    -- liftM2 _,_ in the continuation monad
    _×F_ : ∀ {a b m} {A : ★ a} {B : ★ b} {M : ★ m} → Cont M A → Cont M B → Cont M (A × B)
    fA ×F fB = ΣF fA fB
    -- (fA ×F fB) f = fA (fB ∘ curry f)
    -- (fA ×F fB) f = fA λ x → fB (f (x , y)

ΣSearch : ∀ {m A} {B : A → ★₀} → Search m A → (∀ {x} → Search m (B x)) → Search m (Σ A B)
ΣSearch searchᴬ searchᴮ op = ΣF (searchᴬ op) (searchᴮ op)

ΣSearchInd : ∀ {m p A} {B : A → ★₀}
               {sᴬ : Search m A} {sᴮ : ∀ {x} → Search m (B x)}
             → SearchInd p sᴬ → (∀ {x} → SearchInd p (sᴮ {x})) → SearchInd p (ΣSearch sᴬ sᴮ)
ΣSearchInd Psᴬ Psᴮ P P∙ Pf =
  Psᴬ (λ s → P (λ _ _ → s _ _)) P∙ (λ x → Psᴮ {x} (λ s → P (λ _ _ → s _ _)) P∙ (curry Pf x))

μΣ : ∀ {A} {B : A → ★ _} → Searchable A → (∀ {x} → Searchable (B x)) → Searchable (Σ A B)
μΣ μA μB = _ , ΣSearchInd (search-ind μA) (search-ind μB)

-- using view-search ?
proj₁-search : ∀ {m A} {B : A → ★ _} → Search m (Σ A B) → Search m A
proj₁-search s _∙_ f = s _∙_ (f ∘ proj₁)

proj₂-search : ∀ {m A B} → Search m (A × B) → Search m B
proj₂-search s _∙_ f = s _∙_ (f ∘ proj₂)

-- From now on, these are derived definitions for convenience and pedagogical reasons

ΣSum : ∀ {A} {B : A → ★₀} → Sum A → (∀ {x} → Sum (B x)) → Sum (Σ A B)
ΣSum = ΣF

infixr 4 _×Search_

_×Search_ : ∀ {m A B} → Search m A → Search m B → Search m (A × B)
searchᴬ ×Search searchᴮ = ΣSearch searchᴬ searchᴮ

infixr 4 _×μ_

_×μ_ : ∀ {A B} → Searchable A → Searchable B → Searchable (A × B)
μA ×μ μB = μΣ μA μB

_×SearchInd_ : ∀ {m p A B} {sᴬ : Search m A} {sᴮ : Search m B}
               → SearchInd p sᴬ → SearchInd p sᴮ
               → SearchInd p (sᴬ ×Search sᴮ)
Psᴬ ×SearchInd Psᴮ = ΣSearchInd Psᴬ Psᴮ

infixr 4 _×Sum_

_×Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
sumᴬ ×Sum sumᴮ = ΣSum sumᴬ sumᴮ

module _ {A} {B : A → _} {sᴬ : Search₁ A} {sᴮ : ∀ {x} → Search₁ (B x)} where
  Σ-Σ→Point : Σ→Point sᴬ → (∀ {x} → Σ→Point (sᴮ {x})) → Σ→Point (ΣSearch sᴬ (λ {x} → sᴮ {x}))
  Σ-Σ→Point fᴬ fᴮ ((x , y) , z) = fᴬ (x , fᴮ (y , z))
  Σ-Data→Π : Data→Π sᴬ → (∀ {x} → Data→Π (sᴮ {x})) → Data→Π (ΣSearch sᴬ (λ {x} → sᴮ {x}))
  Σ-Data→Π fᴬ fᴮ g (x , y) = fᴮ (fᴬ g x) y

module _ {A B} {sᴬ : Search₁ A} {sᴮ : Search₁ B} where
  _×Σ→Point_ : Σ→Point sᴬ → Σ→Point sᴮ → Σ→Point (sᴬ ×Search sᴮ)
  (fᴬ ×Σ→Point fᴮ) = Σ-Σ→Point {sᴬ = sᴬ} {sᴮ = sᴮ} fᴬ fᴮ
  _×Data→Π_ : Data→Π sᴬ → Data→Π sᴮ → Data→Π (sᴬ ×Search sᴮ)
  (fᴬ ×Data→Π fᴮ) = Σ-Data→Π {sᴬ = sᴬ} {sᴮ = sᴮ} fᴬ fᴮ

-- Those are here only for pedagogical use
private
    ΣSum' : ∀ {A} {B : A → ★₀} → Sum A → (∀ x → Sum (B x)) → Sum (Σ A B)
    ΣSum' sumᴬ sumᴮ f = sumᴬ (λ x₀ →
                          sumᴮ x₀ (λ x₁ →
                            f (x₀ , x₁)))

    _×Search'_ : ∀ {A B} → Search₀ A → Search _ B → Search _ (A × B)
    (searchᴬ ×Search' searchᴮ) op f = searchᴬ op (λ x → searchᴮ op (curry f x))

    _×SearchInd'_ : ∀ {A B} {sᴬ : Search _ A} {sᴮ : Search _ B}
                    → SearchInd₀ sᴬ → SearchInd₀ sᴮ → SearchInd₀ (sᴬ ×Search' sᴮ)
    (Psᴬ ×SearchInd' Psᴮ) P P∙ Pf =
      Psᴬ (λ s → P (λ _ _ → s _ _)) P∙ (Psᴮ (λ s → P (λ _ _ → s _ _)) P∙ ∘ curry Pf)

    -- liftM2 _,_ in the continuation monad
    _×Sum'_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
    (sumᴬ ×Sum' sumᴮ) f = sumᴬ (λ x₀ →
                            sumᴮ (λ x₁ →
                              f (x₀ , x₁)))
