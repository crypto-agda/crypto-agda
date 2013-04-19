import Level as L
open L using (Lift; lift)
open import Type hiding (★)
open import Function.NP
open import Algebra
open import Algebra.FunctionProperties.NP
open import Data.Nat.NP hiding (_^_)
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)
open import Data.Sum
open import Data.Maybe.NP
open import Data.Product
open import Data.Bits
open import Data.Bool.NP as Bool
open import Data.Fin using (Fin)
open import Function.NP
open import Function.Equality using (_⟨$⟩_)
import Function.Inverse.NP as FI
open FI using (_↔_; inverses; module Inverse) renaming (_$₁_ to to; _$₂_ to from)
import Function.Related as FR
open import Function.Related.TypeIsomorphisms.NP
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_)
open import Search.Type
open import Search.Searchable renaming (Searchable to Searchable)
open import Search.Searchable.Product
open import Search.Searchable.Sum
open import Search.Searchable.Maybe
--open import Search.Searchable.Fin
open import Search.Derived

module sum where

_≈Sum_ : ∀ {A} → (sum₀ sum₁ : Sum A) → ★ _
sum₀ ≈Sum sum₁ = ∀ f → sum₀ f ≡ sum₁ f

_≈Search_ : ∀ {A} → (s₀ s₁ : Search _ A) → ★₁
s₀ ≈Search s₁ = ∀ {B} (op : Op₂ B) f → s₀ op f ≡ s₁ op f

_⊎'_ : ★₀ → ★₀ → ★₀
A ⊎' B = Σ Bool (cond A B)

_μ⊎'_ : ∀ {A B} → Searchable A → Searchable B → Searchable (A ⊎' B)
μA μ⊎' μB = μΣ μBit (λ { {true} → μA ; {false} → μB })

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec.NP as Vec using (Vec; tabulate; _++_) renaming (map to vmap; sum to vsum; foldr to vfoldr; foldr₁ to vfoldr₁)

vmsum : ∀ {c ℓ} (m : Monoid c ℓ) {n} →
          let open Mon m in
          Vec C n → C
vmsum m = vfoldr _ _∙_ ε
  where open Mon m

vsgsum : ∀ {c ℓ} (sg : Semigroup c ℓ) {n} →
           let open Sgrp sg in
           Vec C (suc n) → C
vsgsum sg = vfoldr₁ _∙_
  where open Sgrp sg

-- let's recall that: tabulate f ≗ vmap f (allFin n)

-- searchMonFin : ∀ n → SearchMon (Fin n)
-- searchMonFin n m f = vmsum m (tabulate f)

searchFinSuc : ∀ {m} n → Search m (Fin (suc n))
searchFinSuc n _∙_ f = vfoldr₁ _∙_ (tabulate f)

searchVec : ∀ {m A} n → Search m A → Search m (Vec A n)
searchVec zero    searchᴬ op f = f []
searchVec (suc n) searchᴬ op f = searchᴬ op (λ x → searchVec n searchᴬ op (f ∘ _∷_ x))

searchVec-spec : ∀ {A} (μA : Searchable A) n → searchVec n (search μA) ≈Search search (μVec μA n)
searchVec-spec μA zero    op f = ≡.refl
searchVec-spec μA (suc n) op f = search-ext μA op (λ x → searchVec-spec μA n op (f ∘ _∷_ x))

searchVec-++ : ∀ {A} n {m} (μA : Searchable A) sg
               → let open Sgrp sg in
                 (f : Vec A (n + m) → C)
               → search (μVec μA (n + m)) _∙_ f
               ≈ search (μVec μA n) _∙_ (λ xs →
                   search (μVec μA m) _∙_ (λ ys →
                     f (xs ++ ys)))
searchVec-++ zero    μA sg f = Sgrp.refl sg
searchVec-++ (suc n) μA sg f = search-sg-ext μA sg (λ x →
                                 searchVec-++ n μA sg (f ∘ _∷_ x))

sumVec-swap : ∀ {A} n {m} (μA : Searchable A)(f : Vec A (n + m) → ℕ)
            → sum (μVec μA n) (λ xs → sum (μVec μA m) (λ ys → f (xs ++ ys)))
            ≡ sum (μVec μA m) (λ ys → sum (μVec μA n) (λ xs → f (xs ++ ys)))
sumVec-swap n {m} μA f = sum-swap (μVec μA n) (μVec μA m) (λ xs ys → f (xs ++ ys))

simple : ∀ {A : Set}{P : A → A → Set} → (∀ x → P x x) → {x y : A} → x ≡ y → P x y
simple r ≡.refl = r _
-- -}
-- -}
-- -}
