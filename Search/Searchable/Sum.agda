open import Function.NP
open import Data.Nat using (_+_)
import Level as L
import Function.Inverse.NP as FI
import Function.Related as FR
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP
open import Data.Product.NP
open import Data.Sum
open import Data.Bit
open import Data.Fin using (Fin)
open import Search.Type
open import Search.Searchable

open import Relation.Binary.Sum
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_ ; module ≡-Reasoning; cong)

module Search.Searchable.Sum where

infixr 4 _⊎-search_

_⊎-search_ : ∀ {m A B} → Search m A → Search m B → Search m (A ⊎ B)
(searchᴬ ⊎-search searchᴮ) _∙_ f = searchᴬ _∙_ (f ∘ inj₁) ∙ searchᴮ _∙_ (f ∘ inj₂)

_⊎-search-ind_ : ∀ {m p A B} {sᴬ : Search m A} {sᴮ : Search m B}
                 → SearchInd p sᴬ → SearchInd p sᴮ → SearchInd p (sᴬ ⊎-search sᴮ)
(Psᴬ ⊎-search-ind Psᴮ) P P∙ Pf
  = P∙ (Psᴬ (λ s → P (λ _ f → s _ (f ∘ inj₁))) P∙ (Pf ∘ inj₁))
       (Psᴮ (λ s → P (λ _ f → s _ (f ∘ inj₂))) P∙ (Pf ∘ inj₂))

infixr 4 _⊎-sum_

_⊎-sum_ : ∀ {A B} → Sum A → Sum B → Sum (A ⊎ B)
(sumᴬ ⊎-sum sumᴮ) f = sumᴬ (f ∘ inj₁) + sumᴮ (f ∘ inj₂)

module _ {A B} {sumᴬ : Sum A} {sumᴮ : Sum B} where

    sumᴬᴮ = sumᴬ ⊎-sum sumᴮ

    _⊎-adequate-sum_ : AdequateSum sumᴬ → AdequateSum sumᴮ → AdequateSum sumᴬᴮ
    (asumᴬ ⊎-adequate-sum asumᴮ) f = (Fin (sumᴬ (f ∘ inj₁) + sumᴮ (f ∘ inj₂)))
                                   ↔⟨ FI.sym (Fin-⊎-+ _ _) ⟩
                                     (Fin (sumᴬ (f ∘ inj₁)) ⊎ Fin (sumᴮ (f ∘ inj₂)))
                                   ↔⟨ asumᴬ (f ∘ inj₁) ⊎-cong asumᴮ (f ∘ inj₂) ⟩
                                     (Σ A (Fin ∘ f ∘ inj₁) ⊎ Σ B (Fin ∘ f ∘ inj₂))
                                   ↔⟨ FI.sym Σ⊎-distrib ⟩
                                     Σ (A ⊎ B) (Fin ∘ f)
                                   ∎
      where open FR.EquationalReasoning

_⊎-μ_ : ∀ {A B} → Searchable A → Searchable B → Searchable (A ⊎ B)
μA ⊎-μ μB = mk _ (search-ind μA ⊎-search-ind search-ind μB)
                 (adequate-sum μA ⊎-adequate-sum adequate-sum μB)

module _ {A B} {sᴬ : Search₁ A} {sᴮ : Search₁ B} where
  sᴬ⁺ᴮ = sᴬ ⊎-search sᴮ
  _⊎-focus_ : Focus sᴬ → Focus sᴮ → Focus sᴬ⁺ᴮ
  (fᴬ ⊎-focus fᴮ) (inj₁ x , y) = inj₁ (fᴬ (x , y))
  (fᴬ ⊎-focus fᴮ) (inj₂ x , y) = inj₂ (fᴮ (x , y))

  _⊎-unfocus_ : Unfocus sᴬ → Unfocus sᴮ → Unfocus sᴬ⁺ᴮ
  _⊎-unfocus_ fᴬ fᴮ (inj₁ x) = first inj₁ (fᴬ x)
  _⊎-unfocus_ fᴬ fᴮ (inj₂ y) = first inj₂ (fᴮ y)

  {-
  _⊎-focused_ : Focused sᴬ → Focused sᴮ → Focused {L.zero} sᴬ⁺ᴮ
  _⊎-focused_ fᴬ fᴮ {B} = inverses (to fᴬ ⊎-focus to fᴮ) (from fᴬ ⊎-unfocus from fᴮ) (⇒) (⇐)
      where
        ⇒ : (x : Σ (A ⊎ {!!}) {!!}) → _
        ⇒ (x , y) = {!!}
        ⇐ : (x : sᴬ _⊎_ (B ∘ inj₁) ⊎ sᴮ _⊎_ (B ∘ inj₂)) → _
        ⇐ (inj₁ x) = cong inj₁ {!!}
        ⇐ (inj₂ x) = cong inj₂ {!!}
  -}

  _⊎-lookup_ : Lookup sᴬ → Lookup sᴮ → Lookup (sᴬ ⊎-search sᴮ)
  (lookupᴬ ⊎-lookup lookupᴮ) (x , y) = [ lookupᴬ x , lookupᴮ y ]

  _⊎-reify_ : Reify sᴬ → Reify sᴮ → Reify (sᴬ ⊎-search sᴮ)
  (reifyᴬ ⊎-reify reifyᴮ) f = (reifyᴬ (f ∘ inj₁)) , (reifyᴮ (f ∘ inj₂))

searchBit : ∀ {m} → Search m Bit
searchBit _∙_ f = f 0b ∙ f 1b

searchBit-ind : ∀ {m p} → SearchInd p {m} searchBit
searchBit-ind _ _P∙_ Pf = Pf 0b P∙ Pf 1b

μBit : Searchable Bit
μBit = μ-iso (FI.sym Bit↔⊤⊎⊤) (μ⊤ ⊎-μ μ⊤)

focusBit : ∀ {a} → Focus {a} searchBit
focusBit (0b , x) = inj₁ x
focusBit (1b , x) = inj₂ x

focusedBit : Focused {L.zero} searchBit
focusedBit {B} = inverses focusBit unfocus (⇒) (⇐)
  where open Searchable₁₁ searchBit-ind
        ⇒ : (x : Σ Bit B) → _
        ⇒ (0b , x) = ≡.refl
        ⇒ (1b , x) = ≡.refl
        ⇐ : (x : B 0b ⊎ B 1b) → _
        ⇐ (inj₁ x) = ≡.refl
        ⇐ (inj₂ x) = ≡.refl

lookupBit : ∀ {a} → Lookup {a} searchBit
lookupBit = proj
 -- -}
 -- -}
 -- -}
