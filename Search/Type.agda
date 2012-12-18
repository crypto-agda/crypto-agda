module Search.Type where

open import Level using () renaming (zero to ₀)
open import Type hiding (★)
open import Function.NP
open import Data.Nat.NP
open import Data.Bits
open import Data.Product
open import Data.Sum
open import Algebra
import Algebra.FunctionProperties.NP as FP
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)

module SgrpExtra {c ℓ} (sg : Semigroup c ℓ) where
  open Semigroup sg
  open Setoid-Reasoning (Semigroup.setoid sg) public
  C : ★ _
  C = Carrier
  _≈°_ : ∀ {a} {A : ★ a} (f g : A → C) → ★ _
  f ≈° g = ∀ x → f x ≈ g x
  _∙°_   : ∀ {a} {A : ★ a} (f g : A → C) → A → C
  (f ∙° g) x = f x ∙ g x
  infixl 7 _-∙-_
  _-∙-_ : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  _-∙-_ = ∙-cong

module Sgrp {c ℓ} (sg : Semigroup c ℓ) where
  open Semigroup sg public
  open SgrpExtra sg public

module Mon {c ℓ} (m : Monoid c ℓ) where
  open Monoid m public
  sg = semigroup
  open SgrpExtra semigroup public

module CMon {c ℓ} (cm : CommutativeMonoid c ℓ) where
  open CommutativeMonoid cm public
  sg = semigroup
  m = monoid
  open SgrpExtra sg public
  open FP _≈_

  ∙-interchange : Interchange _∙_ _∙_
  ∙-interchange = InterchangeFromAssocCommCong.∙-interchange
                    isEquivalence
                    _∙_ assoc comm (λ _ → flip ∙-cong refl)

Search : ∀ ℓ → ★₀ → ★ _
Search ℓ A = ∀ {M : ★ ℓ} → (_∙_ : M → M → M) → (A → M) → M

Search₀ : ★₀ → ★₁
Search₀ = Search _

Search₁ : ★₀ → ★₂
Search₁ = Search _

SearchMon : ∀ ℓ r → ★₀ → ★ _
SearchMon ℓ r A = (M : Monoid ℓ r) → let open Mon M in
                                     (A → C) → C

SearchMon₀ : ★₀ → ★ _
SearchMon₀ = SearchMon ₀ ₀

searchMonFromSearch : ∀ {ℓ r A}
                      → Search ℓ A → SearchMon ℓ r A
searchMonFromSearch s m = s _∙_ where open Mon m

Sum : ★₀ → ★₀
Sum A = (A → ℕ) → ℕ

Count : ★₀ → ★₀
Count A = (A → Bit) → ℕ

StableUnder : ∀ {ℓ A} → Search ℓ A → (A → A) → ★ _
StableUnder search p = ∀ {M} op (f : _ → M) → search op f ≡ search op (f ∘ p)

SearchInd : ∀ p {ℓ A} → Search ℓ A → ★ _
SearchInd p {ℓ} {A} srch =
  ∀ (P  : Search ℓ A → ★ p)
    (P∙ : ∀ {s₀ s₁ : Search ℓ A} → P s₀ → P s₁ → P (λ _∙_ f → s₀ _∙_ f ∙ s₁ _∙_ f))
    (Pf : ∀ x → P (λ _ f → f x))
  → P srch

SearchInd₀ : ∀ {ℓ A} → Search ℓ A → ★ _
SearchInd₀ = SearchInd ₀

SumInd : ∀ {A} → Sum A → ★₁
SumInd {A} sum = ∀ (P  : Sum A → ★₀)
                   (P+ : ∀ {s₀ s₁ : Sum A} → P s₀ → P s₁ → P (λ f → s₀ f + s₁ f))
                   (Pf : ∀ x → P (λ f → f x))
                →  P sum

SearchMono : ∀ r {ℓ A} → Search ℓ A → ★ _
SearchMono r sᴬ = ∀ {C} (_⊆_ : C → C → ★ r)
                    {_∙_} (∙-mono : _∙_ Preserves₂ _⊆_ ⟶ _⊆_ ⟶ _⊆_)
                    {f g} →
                    (∀ x → f x ⊆ g x) → sᴬ _∙_ f ⊆ sᴬ _∙_ g

SearchSgExt : ∀ r {ℓ A} → Search ℓ A → ★ _
SearchSgExt r {ℓ} sᴬ = ∀ (sg : Semigroup ℓ r) {f g}
                       → let open Sgrp sg in
                         f ≈° g → sᴬ _∙_ f ≈ sᴬ _∙_ g

SearchExt : ∀ {ℓ A} → Search ℓ A → ★ _
SearchExt {ℓ} {A} sᴬ = ∀ {M} op {f g : A → M} → f ≗ g → sᴬ op f ≡ sᴬ op g

SumExt : ∀ {A} → Sum A → ★ _
SumExt sumᴬ = ∀ {f g} → f ≗ g → sumᴬ f ≡ sumᴬ g

CountExt : ∀ {A} → Count A → ★ _
CountExt countᴬ = ∀ {f g} → f ≗ g → countᴬ f ≡ countᴬ g

Searchε : ∀ {ℓ r A} → SearchMon ℓ r A → ★ _
Searchε sᴬ = ∀ m → let open Mon m in
                   sᴬ m (const ε) ≈ ε

SumZero : ∀ {A} → Sum A → ★ _
SumZero sumᴬ = sumᴬ (λ _ → 0) ≡ 0

SearchLinˡ : ∀ {ℓ r A} → SearchMon ℓ r A → ★ _
SearchLinˡ sᴬ = ∀ m _◎_ f k →
                 let open Mon m
                     open FP _≈_ in
                 _◎_ DistributesOverˡ _∙_ →
                 sᴬ m (λ x → k ◎ f x) ≈ k ◎ sᴬ m f

SearchLinʳ : ∀ {ℓ r A} → SearchMon ℓ r A → ★ _
SearchLinʳ sᴬ = ∀ m _◎_ f k →
                 let open Mon m
                     open FP _≈_ in
                 _◎_ DistributesOverʳ _∙_ →
                 sᴬ m (λ x → f x ◎ k) ≈ sᴬ m f ◎ k

SumLin : ∀ {A} → Sum A → ★ _
SumLin sumᴬ = ∀ f k → sumᴬ (λ x → k * f x) ≡ k * sumᴬ f

SearchHom : ∀ r {ℓ A} → Search ℓ A → ★ _
SearchHom r sᴬ = ∀ sg f g → let open Sgrp {_} {r} sg in
                            sᴬ _∙_ (f ∙° g) ≈ sᴬ _∙_ f ∙ sᴬ _∙_ g

SearchMonHom : ∀ {ℓ r A} → SearchMon ℓ r A → ★ _
SearchMonHom sᴬ = ∀ cm f g →
                    let open CMon cm in
                    sᴬ m (f ∙° g) ≈ sᴬ m f ∙ sᴬ m g

SumHom : ∀ {A} → Sum A → ★ _
SumHom sumᴬ = ∀ f g → sumᴬ (λ x → f x + g x) ≡ sumᴬ f + sumᴬ g

SumMono : ∀ {A} → Sum A → ★ _
SumMono sumᴬ = ∀ {f g} → f ≤° g → sumᴬ f ≤ sumᴬ g

SearchSwap : ∀ r {ℓ A} → Search ℓ A → ★ _
SearchSwap r {ℓ} {A} sᴬ = ∀ {B : ★₀} sg f →
                            let open Sgrp {_} {r} sg in
                          ∀ {sᴮ : (B → C) → C}
                          → (hom : ∀ f g → sᴮ (f ∙° g) ≈ sᴮ f ∙ sᴮ g)
                          → sᴬ _∙_ (sᴮ ∘ f) ≈ sᴮ (sᴬ _∙_ ∘ flip f)

Data : ∀ {b A} → Search _ A → (A → ★ b) → ★ b
Data sA = sA _×_

DataToFun : ∀ {b A} → Search _ A → ★ _
DataToFun {b} {A} sA = ∀ {B : A → ★ b} → Data sA B → Π A B

DataFromFun : ∀ {b A} → Search _ A → ★ _
DataFromFun {b} {A} sA = ∀ {B : A → ★ b} → Π A B → Data sA B

Point : ∀ {b A} → Search _ A → (A → ★ b) → ★ b
Point sA = sA _⊎_

PointToPair : ∀ {b A} → Search _ A → ★ _
PointToPair {b} {A} sA = ∀ {B : A → ★ b} → Point sA B → Σ A B

PointFromPair : ∀ {b A} → Search _ A → ★ _
PointFromPair {b} {A} sA = ∀ {B : A → ★ b} → Σ A B → Point sA B
