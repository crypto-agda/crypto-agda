open import Type hiding (★)
open import Function
open import Search.Type
open import Algebra.FunctionProperties.NP
open import Data.Bool.NP as Bool
open import Data.Nat.NP hiding (_^_)
open import Data.Nat.Properties
open import Data.Product
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module Search.Searchable where

record Searchable A : ★₁ where
  constructor _,_
  field
    search     : Search A
    search-ind : SearchInd search

  search-sg-ext : SearchSgExt search
  search-sg-ext sg {f} {g} f≈°g = search-ind (λ s → s _ f ≈ s _ g) ∙-cong f≈°g
    where open Sgrp sg

  search-ext : SearchExt search
  search-ext op = search-ind (λ s → s _ _ ≡ s _ _) (≡.cong₂ op)

  search-mono : SearchMono search
  search-mono _⊆_ _∙-mono_ {f} {g} f⊆°g = search-ind (λ s → s _ f ⊆ s _ g) _∙-mono_ f⊆°g

  search-swap : SearchSwap search
  search-swap sg f {sᴮ} pf = search-ind (λ s → s _ (sᴮ ∘ f) ≈ sᴮ (s _ ∘ flip f)) (λ p q → trans (∙-cong p q) (sym (pf _ _))) (λ _ → refl)
    where open Sgrp sg

  searchMon : SearchMon A
  searchMon m = search _∙_
    where open Mon m

  search-ε : Searchε searchMon
  search-ε m = search-ind (λ s → s _ (const ε) ≈ ε) (λ x≈ε y≈ε → trans (∙-cong x≈ε y≈ε) (proj₁ identity ε)) (λ _ → refl)
    where open Mon m

  search-hom : SearchMonHom searchMon
  search-hom cm f g = search-ind (λ s → s _ (f ∙° g) ≈ s _ f ∙ s _ g)
                                 (λ p₀ p₁ → trans (∙-cong p₀ p₁) (∙-interchange _ _ _ _)) (λ _ → refl)
    where open CMon cm

  search-hom′ :
      ∀ {S T}
        (_+_ : Op₂ S)
        (_*_ : Op₂ T)
        (f   : S → T)
        (g   : A → S)
        (hom : ∀ x y → f (x + y) ≡ f x * f y)
        → f (search _+_ g) ≡ search _*_ (f ∘ g)
  search-hom′ _+_ _*_ f g hom = search-ind (λ s → f (s _+_ g) ≡ s _*_ (f ∘ g))
                                           (λ p q → ≡.trans (hom _ _) (≡.cong₂ _*_ p q))
                                           (λ _ → ≡.refl)

  StableUnder : (A → A) → ★₁
  StableUnder p = ∀ {B} (op : Op₂ B) f → search op f ≡ search op (f ∘ p)

  sum : Sum A
  sum = search _+_

  sum-ind : SumInd sum
  sum-ind P P+ Pf = search-ind (λ s → P (s _+_)) P+ Pf

  sum-ext : SumExt sum
  sum-ext = search-ext _+_

  sum-zero : SumZero sum
  sum-zero = search-ε ℕ+.monoid

  sum-hom : SumHom sum
  sum-hom = search-hom ℕ°.+-commutativeMonoid

  sum-mono : SumMono sum
  sum-mono = search-mono _≤_ _+-mono_

  sum-lin : SumLin sum
  sum-lin f zero    = sum-zero
  sum-lin f (suc k) = ≡.trans (sum-hom f (λ x → k * f x)) (≡.cong₂ _+_ (≡.refl {x = sum f}) (sum-lin f k))

  SumStableUnder : (A → A) → ★ _
  SumStableUnder p = ∀ f → sum f ≡ sum (f ∘ p)

  sumStableUnder : ∀ {p} → StableUnder p → SumStableUnder p
  sumStableUnder SU-p = SU-p _+_

  Card : ℕ
  Card = sum (const 1)

  count : Count A
  count f = sum (Bool.toℕ ∘ f)

  count-ext : CountExt count
  count-ext f≗g = sum-ext (≡.cong Bool.toℕ ∘ f≗g)

  CountStableUnder : (A → A) → ★ _
  CountStableUnder p = ∀ f → count f ≡ count (f ∘ p)

  countStableUnder : ∀ {p} → SumStableUnder p → CountStableUnder p
  countStableUnder sumSU-p f = sumSU-p (Bool.toℕ ∘ f)

open Searchable public
