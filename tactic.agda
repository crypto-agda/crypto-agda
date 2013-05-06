module tactic where

open import Type
open import Search.Type
open import Search.Searchable
open import Search.Searchable.Product

open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality.NP

module _ {R S} (sum-R : Sum R)(sum-R-ext : SumExt sum-R)(sum-S : Sum S) where
  su-× : ∀ {f : R → R}{g : S → S} → SumStableUnder sum-R f → SumStableUnder sum-S g
       → SumStableUnder (sum-R ×-sum sum-S) (map f g)
  su-× {f}{g} su-f su-g F
    = (sum-R ×-sum sum-S) F
    ≡⟨ sum-R-ext (λ x → su-g (λ y → F ( x , y))) ⟩
      (sum-R ×-sum sum-S) (F ∘ map id g)
    ≡⟨ su-f (λ x → sum-S (λ y → F (map id g (x , y)))) ⟩
      (sum-R ×-sum sum-S) (F ∘ map f g)
    ∎ where open ≡-Reasoning

module _ {R}(sum-R : Sum R) where
  su-id : SumStableUnder sum-R id
  su-id f = refl

  su-∘ : ∀ {f g} → SumStableUnder sum-R f → SumStableUnder sum-R g → SumStableUnder sum-R (f ∘ g)
  su-∘ {f} su-f su-g F = trans (su-f F) (su-g (F ∘ f))

module _ {R R' S'}(sum-R : Sum R)(sum-R' : Sum R')(sum-S' : Sum S')(sum-R'-ext : SumExt sum-R')
           (h : R' → R')(su-h : SumStableUnder sum-R' h)
           (to : R' → S' → R)(sum-same : ∀ f → sum-R f ≡ sum-R' (λ r' → sum-S' (f ∘ to r'))) where

  principle : ∀ {f g} → (∀ r' → sum-S' (f ∘ to r') ≡ sum-S' (g ∘ to (h r'))) → sum-R f ≡ sum-R g
  principle {f}{g} prf
    = sum-R f
    ≡⟨ sum-same f ⟩
      sum-R' (λ r' → sum-S' (λ s' → f (to r' s')))
    ≡⟨ sum-R'-ext (λ r' → prf r') ⟩
      sum-R' (λ r' → sum-S' (λ s' → g (to (h r') s')))
    ≡⟨ sym (su-h (λ r' → sum-S' (λ s' → g (to r' s')))) ⟩
      sum-R' (λ r' → sum-S' (λ s' → g (to r' s')))
    ≡⟨ sym (sum-same g) ⟩
      sum-R g
    ∎
    where open ≡-Reasoning
  
