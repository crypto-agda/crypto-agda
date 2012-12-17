open import Type hiding (★)
open import Function.NP
open import Data.Product
open import Search.Type
open import Search.Searchable

module Search.Searchable.Product where

private
    Cont : ★₀ → ★₀ → ★₀
    Cont M A = (A → M) → M

    -- liftM2 _,_ in the continuation monad
    _×F_ : ∀ {A B M} → Cont M A → Cont M B → Cont M (A × B)
    (fA ×F fB) f = fA (fB ∘ curry f)
    -- (fA ×F fB) f = fA λ x → fB (f (x , y)

    ΣF : ∀ {A B M} → Cont M A → (∀ {x} → Cont M (B x)) → Cont M (Σ A B)
    ΣF fA fB f = fA (fB ∘ curry f)

ΣSearch : ∀ {A} {B : A → ★₀} → Search A → (∀ {x} → Search (B x)) → Search (Σ A B)
ΣSearch searchᴬ searchᴮ op = ΣF (searchᴬ op) (searchᴮ op)

ΣSearchInd : ∀ {A} {B : A → ★₀}
               {sᴬ : Search A} {sᴮ : ∀ {x} → Search (B x)}
             → SearchInd sᴬ → (∀ {x} → SearchInd (sᴮ {x})) → SearchInd (ΣSearch sᴬ sᴮ)
ΣSearchInd Psᴬ Psᴮ P P∙ Pf =
  Psᴬ (λ s → P (λ _ _ → s _ _)) P∙ (λ x → Psᴮ {x} (λ s → P (λ _ _ → s _ _)) P∙ (curry Pf x))

μΣ : ∀ {A} {B : A → ★ _} → Searchable A → (∀ {x} → Searchable (B x)) → Searchable (Σ A B)
μΣ μA μB = _ , ΣSearchInd (search-ind μA) (search-ind μB)

-- From now on, these are derived definitions for convenience and pedagogical reasons

ΣSum : ∀ {A} {B : A → ★₀} → Sum A → (∀ {x} → Sum (B x)) → Sum (Σ A B)
ΣSum = ΣF

infixr 4 _×Search_

_×Search_ : ∀ {A B} → Search A → Search B → Search (A × B)
searchᴬ ×Search searchᴮ = ΣSearch searchᴬ searchᴮ

infixr 4 _×μ_

_×μ_ : ∀ {A B} → Searchable A → Searchable B → Searchable (A × B)
μA ×μ μB = μΣ μA μB

infixr 4 _×Sum_

_×Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
sumᴬ ×Sum sumᴮ = ΣSum sumᴬ sumᴮ

-- Those are here only for pedagogical use
private
    ΣSum' : ∀ {A} {B : A → ★₀} → Sum A → (∀ x → Sum (B x)) → Sum (Σ A B)
    ΣSum' sumᴬ sumᴮ f = sumᴬ (λ x₀ →
                          sumᴮ x₀ (λ x₁ →
                            f (x₀ , x₁)))

    _×Search'_ : ∀ {A B} → Search A → Search B → Search (A × B)
    (searchᴬ ×Search' searchᴮ) op f = searchᴬ op (λ x → searchᴮ op (curry f x))

    _×SearchInd'_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B}
                    → SearchInd sᴬ → SearchInd sᴮ → SearchInd (sᴬ ×Search' sᴮ)
    (Psᴬ ×SearchInd' Psᴮ) P P∙ Pf =
      Psᴬ (λ s → P (λ _ _ → s _ _)) P∙ (Psᴮ (λ s → P (λ _ _ → s _ _)) P∙ ∘ curry Pf)

    -- liftM2 _,_ in the continuation monad
    _×Sum'_ : ∀ {A B} → Sum A → Sum B → Sum (A × B)
    (sumᴬ ×Sum' sumᴮ) f = sumᴬ (λ x₀ →
                            sumᴮ (λ x₁ →
                              f (x₀ , x₁)))
