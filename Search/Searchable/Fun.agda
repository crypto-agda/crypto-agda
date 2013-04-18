module Search.Searchable.Fun where

open import Type hiding (★)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Bits
open import Function.NP
open import Search.Type
open import Search.Searchable
open import Search.Searchable.Product
open import Search.Searchable.Sum
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
open import Function.Related.TypeIsomorphisms.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_)

private -- unused
    SΠΣ⁻ : ∀ {m A} {B : A → ★ _} {C : Σ A B → ★ _}
           → Search m ((x : A) (y : B x) → C (x , y))
           → Search m (Π (Σ A B) C)
    SΠΣ⁻ s _∙_ f = s _∙_ (f ∘ uncurry)

    SΠΣ⁻-ind : ∀ {m p A} {B : A → ★ _} {C : Σ A B → ★ _}
               → {s : Search m ((x : A) (y : B x) → C (x , y))}
               → SearchInd p s
               → SearchInd p (SΠΣ⁻ s)
    SΠΣ⁻-ind ind P P∙ Pf = ind (P ∘ SΠΣ⁻) P∙ (Pf ∘ uncurry)

    S×⁻ : ∀ {m A B C} → Search m (A → B → C) → Search m (A × B → C)
    S×⁻ = SΠΣ⁻

    S×⁻-ind : ∀ {m p A B C}
              → {s : Search m (A → B → C)}
              → SearchInd p s
              → SearchInd p (S×⁻ s)
    S×⁻-ind = SΠΣ⁻-ind

    SΠ⊎⁻ : ∀ {m A B} {C : A ⊎ B → ★ _}
           → Search m (Π A (C ∘ inj₁) × Π B (C ∘ inj₂))
           → Search m (Π (A ⊎ B) C)
    SΠ⊎⁻ s _∙_ f = s _∙_ (f ∘ uncurry [_,_])

    SΠ⊎⁻-ind : ∀ {m p A B} {C : A ⊎ B → ★ _}
                 {s : Search m (Π A (C ∘ inj₁) × Π B (C ∘ inj₂))}
                 (i : SearchInd p s)
               → SearchInd p (SΠ⊎⁻ {C = C} s) -- A sB)
    SΠ⊎⁻-ind i P P∙ Pf = i (P ∘ SΠ⊎⁻) P∙ (Pf ∘ uncurry [_,_])

    {- For each A→C function
       and each B→C function
       an A⊎B→C function is yield
     -}
    S⊎⁻ : ∀ {m A B C} → Search m (A → C) → Search m (B → C)
                      → Search m (A ⊎ B → C)
    S⊎⁻ sA sB =  SΠ⊎⁻ (sA ×-search sB)

μΠΣ⁻ : ∀ {A B}{C : Σ A B → ★₀} → Searchable ((x : A)(y : B x) → C (x , y)) → Searchable (Π (Σ A B) C)
μΠΣ⁻ = μ-iso (FI.sym curried)

Σ-Fun : ∀ {A B} → Funable A → Funable B → Funable (A × B)
Σ-Fun (μA , μA→) FB  = μΣ μA (searchable FB) , (λ x → μΠΣ⁻ (μA→ (negative FB x)))
  where open Funable

{-
μΠ⊎⁻ : ∀ {A B : ★₀}{C : A ⊎ B → ★ _} → Searchable (Π A (C ∘ inj₁) × Π B (C ∘ inj₂))
     → Searchable (Π (A ⊎ B) C)
μΠ⊎⁻ = μ-iso ?

_⊎-Fun_ : ∀ {A B : ★₀} → Funable A → Funable B → Funable (A ⊎ B)
_⊎-Fun_ (μA , μA→) (μB , μB→) = (μA ⊎-μ μB) , (λ X → μΠ⊎⁻ (μA→ X ×-μ μB→ X))
-}

S⊤ : ∀ {m A} → Search m A → Search m (⊤ → A)
S⊤ sA _∙_ f = sA _∙_ (f ∘ const)

SΠBit : ∀ {m A} → Search m (A 0b) → Search m (A 1b)
                → Search m (Π Bit A)
SΠBit sA₀ sA₁ _∙_ f = sA₀ _∙_ λ x → sA₁ _∙_ λ y → f λ {true → y; false → x}

×-Dist : ∀ {A B} FA FB → DistFunable {A} FA → DistFunable {B} FB → DistFunable (Σ-Fun FA FB)
×-Dist FA FB FA-dist FB-dist μX c _⊙_ distrib _⊙-cong_ f
  = Πᴬ (λ x → Πᴮ (λ y → Σ' (f (x , y))))
  ≈⟨ ⟦search⟧ (searchable FA){_≡_} ≡.refl _≈_ (λ x y → x ⊙-cong y)
       (λ { {x} {.x} ≡.refl → FB-dist μX c _⊙_ distrib _⊙-cong_ (curry f x)}) ⟩
    Πᴬ (λ x → Σᴮ (λ fb → Πᴮ (λ y → f (x , y) (fb y))))
  ≈⟨ FA-dist (negative FB μX) c _⊙_ distrib _⊙-cong_
       (λ x fb → search (searchable FB) _⊙_ (λ y → f (x , y) (fb y))) ⟩
    Σᴬᴮ (λ fab → Πᴬ (λ x → Πᴮ (λ y → f (x , y) (fab x y))))
  ∎
  where
    open CMon c
    open Funable

    Σ' = search μX _∙_

    Πᴬ = search (searchable FA) _⊙_
    Πᴮ = search (searchable FB) _⊙_

    Σᴬᴮ = search (negative FA (negative FB μX)) _∙_
    Σᴮ  = search (negative FB μX) _∙_

    {-
⊎-Dist : ∀ {A B : ★₀} FA FB → DistFunable {A} FA → DistFunable {B} FB → DistFunable (FA ⊎-Fun FB)
⊎-Dist FA FB FA-dist FB-dist μX c _◎_ distrib _◎-cong_ f
 = Πᴬ (Σ' ∘ f ∘ inj₁) ◎ Πᴮ (Σ' ∘ f ∘ inj₂)
 ≈⟨ {!FA-dist μX c _◎_ distrib _◎-cong_ (f ∘ inj₁) ◎-cong FB-dist μX c _◎_ distrib _◎-cong_ (f ∘ inj₂)!} ⟩
 {-
   Σᴬ (λ fa → Πᴬ (λ i → f (inj₁ i) (fa i))) ◎ Σᴮ (λ fb → Πᴮ (λ i → f (inj₂ i) (fb i)))
 ≈⟨ sym (search-linʳ (negative FA μX) monoid _◎_ _ _ (proj₂ distrib)) ⟩
   Σᴬ (λ fa → Πᴬ (λ i → f (inj₁ i) (fa i)) ◎ Σᴮ (λ fb → Πᴮ (λ i → f (inj₂ i) (fb i))))
 ≈⟨ search-sg-ext (negative FA μX) semigroup (λ fa → sym (search-linˡ (negative FB μX) monoid _◎_ _ _ (proj₁ distrib))) ⟩
 -}
   (Σᴬ λ fa → Σᴮ λ fb → Πᴬ ((f ∘ inj₁) ˢ fa) ◎ Πᴮ ((f ∘ inj₂) ˢ fb))
 ∎
 where
    open CMon c
    open Funable

    Σ' = search μX _∙_

    Πᴬ = search (searchable FA) _◎_
    Πᴮ = search (searchable FB) _◎_

    Σᴬ = search (negative FA μX) _∙_
    Σᴮ = search (negative FB μX) _∙_
-}

-- -}
-- -}
-- -}
