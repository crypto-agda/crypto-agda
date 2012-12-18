module Search.Type where

import Level as L
open import Type
open import Function
open import Data.Nat
open import Data.Bits
open import Algebra
open import Algebra.FunctionProperties.NP
open import Relation.Binary.NP
{-
open import Data.Nat.NP hiding (_^_)
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Maybe.NP
open import Data.Product
open import Data.Bool.NP as Bool
open import Function.Equality using (_⟨$⟩_)
import Function.Inverse as FI
open FI using (_↔_; module Inverse)
import Function.Related as FR
open import Function.Related.TypeIsomorphisms.NP
open import Relation.Binary.NP
-}
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)

_≤°_ : ∀ {A : ★}(f g : A → ℕ) → ★
f ≤° g = ∀ x → f x ≤ g x

Semigroup₀ = Semigroup L.zero L.zero
Monoid₀ = Monoid L.zero L.zero
CommutativeMonoid₀ = CommutativeMonoid L.zero L.zero

module SgrpExtra (sg : Semigroup₀) where
  open Semigroup sg
  open Setoid-Reasoning (Semigroup.setoid sg) public
  C : ★
  C = Carrier
  _≈°_ : ∀ {A : ★} (f g : A → C) → ★
  f ≈° g = ∀ x → f x ≈ g x
  _∙°_   : ∀ {A : ★} (f g : A → C) → A → C
  (f ∙° g) x = f x ∙ g x
  infixl 7 _-∙-_
  _-∙-_ : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  _-∙-_ = ∙-cong

module Sgrp (sg : Semigroup₀) where
  open Semigroup sg public
  open SgrpExtra sg public

module Mon (m : Monoid₀) where
  open Monoid m public
  sg = semigroup
  open SgrpExtra semigroup public

module CMon (cm : CommutativeMonoid₀) where
  open CommutativeMonoid cm public
  sg = semigroup
  m = monoid
  open SgrpExtra sg public

  ∙-interchange : Interchange _≈_ _∙_ _∙_
  ∙-interchange = InterchangeFromAssocCommCong.∙-interchange
                    _≈_ isEquivalence
                    _∙_ assoc comm (λ _ → flip ∙-cong refl)

Search : ★ → ★₁
Search A = ∀ {B} → (_∙_ : B → B → B) → (A → B) → B
-- Search A = ∀ {I : ★} {F : I → ★} → (_∙_ : ∀ {i} → F i → F i → F i) → ∀ {i} → (A → F i) → F i

SearchMon : ★ → ★₁
SearchMon A = (m : Monoid₀) → let open Mon m in
                              (A → C) → C

searchMonFromSearch : ∀ {A} → Search A → SearchMon A
searchMonFromSearch s m = s _∙_ where open Mon m

Sum : ★ → ★
Sum A = (A → ℕ) → ℕ

Count : ★ → ★
Count A = (A → Bit) → ℕ

SearchInd : ∀ {A} → Search A → ★₁
SearchInd {A} srch = ∀ (P  : Search A → ★)
                       (P∙ : ∀ {s₀ s₁ : Search A} → P s₀ → P s₁ → P (λ _∙_ f → s₀ _∙_ f ∙ s₁ _∙_ f))
                       (Pf : ∀ x → P (λ _ f → f x))
                     →  P srch

SumInd : ∀ {A} → Sum A → ★₁
SumInd {A} sum = ∀ (P  : Sum A → ★)
                   (P+ : ∀ {s₀ s₁ : Sum A} → P s₀ → P s₁ → P (λ f → s₀ f + s₁ f))
                   (Pf : ∀ x → P (λ f → f x))
                →  P sum

SearchMono : ∀ {A} → Search A → ★₁
SearchMono sᴬ = ∀ {C} (_⊆_ : C → C → ★) →
                ∀ {_∙_} (∙-mono : _∙_ Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_)
                  {f g} →
                  (∀ x → f x ⊆ g x) → sᴬ _∙_ f ⊆ sᴬ _∙_ g

SearchSgExt : ∀ {A} → Search A → ★₁
SearchSgExt sᴬ = ∀ sg {f g} → let open Sgrp sg in
                              f ≈° g → sᴬ _∙_ f ≈ sᴬ _∙_ g

SearchExt : ∀ {A} → Search A → ★₁
SearchExt {A} sᴬ = ∀ {B} op {f g : A → B} → f ≗ g → sᴬ op f ≡ sᴬ op g

SumExt : ∀ {A} → Sum A → ★
SumExt sumᴬ = ∀ {f g} → f ≗ g → sumᴬ f ≡ sumᴬ g

CountExt : ∀ {A} → Count A → ★
CountExt countᴬ = ∀ {f g} → f ≗ g → countᴬ f ≡ countᴬ g

Searchε : ∀ {A} → SearchMon A → ★₁
Searchε sᴬ = ∀ m → let open Mon m in
                   sᴬ m (const ε) ≈ ε

SumZero : ∀ {A} → Sum A → ★
SumZero sumᴬ = sumᴬ (λ _ → 0) ≡ 0

SearchLinˡ : ∀ {A} → SearchMon A → ★₁
SearchLinˡ sᴬ = ∀ m _◎_ f k → let open Mon m in
                 _DistributesOverˡ_ _≈_ _◎_ _∙_ →
                 sᴬ m (λ x → k ◎ f x) ≈ k ◎ sᴬ m f

SearchLinʳ : ∀ {A} → SearchMon A → ★₁
SearchLinʳ sᴬ = ∀ m _◎_ f k → let open Mon m in
                 _DistributesOverʳ_ _≈_ _◎_ _∙_ →
                 sᴬ m (λ x → f x ◎ k) ≈ sᴬ m f ◎ k

SumLin : ∀ {A} → Sum A → ★
SumLin sumᴬ = ∀ f k → sumᴬ (λ x → k * f x) ≡ k * sumᴬ f

SearchHom : ∀ {A} → Search A → ★₁
SearchHom sᴬ = ∀ sg f g → let open Sgrp sg in
                          sᴬ _∙_ (f ∙° g) ≈ sᴬ _∙_ f ∙ sᴬ _∙_ g

SearchMonHom : ∀ {A} → SearchMon A → ★₁
SearchMonHom sᴬ = ∀ (cm : CommutativeMonoid₀) f g →
                         let open CMon cm in
                         sᴬ m (f ∙° g) ≈ sᴬ m f ∙ sᴬ m g

SumHom : ∀ {A} → Sum A → ★
SumHom sumᴬ = ∀ f g → sumᴬ (λ x → f x + g x) ≡ sumᴬ f + sumᴬ g

SumMono : ∀ {A} → Sum A → ★
SumMono sumᴬ = ∀ {f g} → f ≤° g → sumᴬ f ≤ sumᴬ g

SearchSwap : ∀ {A} → Search A → ★₁
SearchSwap {A} sᴬ = ∀ {B} sg f →
                    let open Sgrp sg in ∀ {sᴮ : (B → C) → C}
                  → (hom : ∀ f g → sᴮ (f ∙° g) ≈ sᴮ f ∙ sᴮ g)
                  → sᴬ _∙_ (sᴮ ∘ f) ≈ sᴮ (sᴬ _∙_ ∘ flip f)
