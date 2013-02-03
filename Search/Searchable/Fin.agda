module Search.Searchable.Fin where

open import Function
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat

open import Search.Type
open import Search.Searchable

module _ {A : Set}(μA : Searchable A) where

  sA = search μA

  extend : ∀ {n} → A → (Fin n → A) → Fin (suc n) → A
  extend x g zero    = x
  extend x g (suc i) = g i

  ¬Fin0 : Fin 0 → A
  ¬Fin0 ()

  -- There is one function Fin 0 → A (called abs) so this should be fine
  -- if not there is a version below that forces the domain to be non-empty
  sFun : ∀ n → Search _ (Fin n → A)
  sFun zero    op f = f ¬Fin0
  sFun (suc n) op f = sA op (λ x → sFun n op (f ∘ extend x))

  ind : ∀ n → SearchInd _ (sFun n)
  ind zero    P P∙ Pf = Pf _
  ind (suc n) P P∙ Pf =
    search-ind μA (λ sa → P (λ op f → sa op (λ x → sFun n op (f ∘ extend x))))
      P∙
      (λ x → ind n (λ sf → P (λ op f → sf op (f ∘ extend x)))
        P∙ (Pf ∘ extend x))

  μFun : ∀ {n} → Searchable (Fin n → A)
  μFun = mk _ (ind _) {!!}
