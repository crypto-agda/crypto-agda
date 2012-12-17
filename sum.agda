import Level as L
open L using (Lift)
open import Type hiding (★)
open import Function
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
open import Function.Equality using (_⟨$⟩_)
import Function.Inverse as FI
open FI using (_↔_; module Inverse)
import Function.Related as FR
open import Function.Related.TypeIsomorphisms.NP
open import Relation.Binary.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)
open import Search.Type
open import Search.Searchable renaming (Searchable to SumProp)
open import Search.Searchable.Product

module sum where

sum-lin⇒sum-zero : ∀ {A} → {sum : Sum A} → SumLin sum → SumZero sum
sum-lin⇒sum-zero sum-lin = sum-lin (λ _ → 0) 0

sum-mono⇒sum-ext : ∀ {A} → {sum : Sum A} → SumMono sum → SumExt sum
sum-mono⇒sum-ext sum-mono f≗g = ℕ≤.antisym (sum-mono (ℕ≤.reflexive ∘ f≗g)) (sum-mono (ℕ≤.reflexive ∘ ≡.sym ∘ f≗g))

sum-ext+sum-hom⇒sum-mono : ∀ {A} → {sum : Sum A} → SumExt sum → SumHom sum → SumMono sum
sum-ext+sum-hom⇒sum-mono {sum = sum} sum-ext sum-hom {f} {g} f≤°g =
    sum f                         ≤⟨ m≤m+n _ _ ⟩
    sum f + sum (λ x → g x ∸ f x) ≡⟨ ≡.sym (sum-hom _ _) ⟩
    sum (λ x → f x + (g x ∸ f x)) ≡⟨ sum-ext (m+n∸m≡n ∘ f≤°g) ⟩
    sum g ∎ where open ≤-Reasoning

search-swap' : ∀ {A B} cm (μA : SumProp A) (μB : SumProp B) f →
               let open CMon cm
                   sᴬ = search μA _∙_
                   sᴮ = search μB _∙_ in
               sᴬ (sᴮ ∘ f) ≈ sᴮ (sᴬ ∘ flip f)
search-swap' cm μA μB f = search-swap μA sg f (search-hom μB cm)
  where open CMon cm

sum-swap : ∀ {A B} (μA : SumProp A) (μB : SumProp B) f →
           sum μA (sum μB ∘ f) ≡ sum μB (sum μA ∘ flip f)
sum-swap = search-swap' ℕ°.+-commutativeMonoid

_≈Sum_ : ∀ {A} → (sum₀ sum₁ : Sum A) → ★ _
sum₀ ≈Sum sum₁ = ∀ f → sum₀ f ≡ sum₁ f

_≈Search_ : ∀ {A} → (s₀ s₁ : Search A) → ★₁
s₀ ≈Search s₁ = ∀ {B} (op : Op₂ B) f → s₀ op f ≡ s₁ op f

μLift⊤ : SumProp (Lift ⊤)
μLift⊤ = _ , ind
  where
    srch : Search (Lift ⊤)
    srch _ f = f _

    ind : SearchInd srch
    ind _ _ Pf = Pf _

μ⊤ : SumProp ⊤
μ⊤ = srch , ind
  where
    srch : Search ⊤
    srch _ f = f _

    ind : SearchInd srch
    ind _ _ Pf = Pf _

μBit : SumProp Bit
μBit = searchBit , ind
  where
    searchBit : Search Bit
    searchBit _∙_ f = f 0b ∙ f 1b

    ind : SearchInd searchBit
    ind _ _P∙_ Pf = Pf 0b P∙ Pf 1b

infixr 4 _+Search_

_+Search_ : ∀ {A B} → Search A → Search B → Search (A ⊎ B)
(searchᴬ +Search searchᴮ) _∙_ f = searchᴬ _∙_ (f ∘ inj₁) ∙ searchᴮ _∙_ (f ∘ inj₂)

_+SearchInd_ : ∀ {A B} {sᴬ : Search A} {sᴮ : Search B} →
                 SearchInd sᴬ → SearchInd sᴮ → SearchInd (sᴬ +Search sᴮ)
(Psᴬ +SearchInd Psᴮ) P P∙ Pf
  = P∙ (Psᴬ (λ s → P (λ _ f → s _ (f ∘ inj₁))) P∙ (Pf ∘ inj₁))
       (Psᴮ (λ s → P (λ _ f → s _ (f ∘ inj₂))) P∙ (Pf ∘ inj₂))

infixr 4 _+Sum_

_+Sum_ : ∀ {A B} → Sum A → Sum B → Sum (A ⊎ B)
(sumᴬ +Sum sumᴮ) f = sumᴬ (f ∘ inj₁) + sumᴮ (f ∘ inj₂)

_+μ_ : ∀ {A B} → SumProp A → SumProp B → SumProp (A ⊎ B)
μA +μ μB = _ , search-ind μA +SearchInd search-ind μB


_⊎'_ : ★₀ → ★₀ → ★₀
A ⊎' B = Σ Bool (cond A B)

_μ⊎'_ : ∀ {A B} → SumProp A → SumProp B → SumProp (A ⊎' B)
μA μ⊎' μB = μΣ μBit (λ { {true} → μA ; {false} → μB })

sum-const : ∀ {A} (μA : SumProp A) → ∀ k → sum μA (const k) ≡ Card μA * k
sum-const μA k
  rewrite ℕ°.*-comm (Card μA) k
        | ≡.sym (sum-lin μA (const 1) k)
        | proj₂ ℕ°.*-identity k = ≡.refl

infixr 4 _×Sum-proj₁_ _×Sum-proj₁'_ _×Sum-proj₂_ _×Sum-proj₂'_

_×Sum-proj₁_ : ∀ {A B}
                 (μA : SumProp A)
                 (μB : SumProp B)
                 f →
                 sum (μA ×μ μB) (f ∘ proj₁) ≡ Card μB * sum μA f
(μA ×Sum-proj₁ μB) f
  rewrite sum-ext μA (sum-const μB ∘ f)
        = sum-lin μA f (Card μB)

_×Sum-proj₂_ : ∀ {A B}
                 (μA : SumProp A)
                 (μB : SumProp B)
                 f →
                 sum (μA ×μ μB) (f ∘ proj₂) ≡ Card μA * sum μB f
(μA ×Sum-proj₂ μB) f = sum-const μA (sum μB f)

_×Sum-proj₁'_ : ∀ {A B}
                  (μA : SumProp A) (μB : SumProp B)
                  {f} {g} →
                  sum μA f ≡ sum μA g →
                  sum (μA ×μ μB) (f ∘ proj₁) ≡ sum (μA ×μ μB) (g ∘ proj₁)
(μA ×Sum-proj₁' μB) {f} {g} sumf≡sumg
  rewrite (μA ×Sum-proj₁ μB) f
        | (μA ×Sum-proj₁ μB) g
        | sumf≡sumg = ≡.refl

_×Sum-proj₂'_ : ∀ {A B}
                  (μA : SumProp A) (μB : SumProp B)
                  {f} {g} →
                  sum μB f ≡ sum μB g →
                  sum (μA ×μ μB) (f ∘ proj₂) ≡ sum (μA ×μ μB) (g ∘ proj₂)
(μA ×Sum-proj₂' μB) sumf≡sumg = sum-ext μA (const sumf≡sumg)

μ-view : ∀ {A B} → (A → B) → SumProp A → SumProp B
μ-view {A}{B} A→B μA = searchᴮ , ind
  where
    searchᴮ : Search B
    searchᴮ m f = search μA m (f ∘ A→B)

    ind : SearchInd searchᴮ
    ind P P∙ Pf = search-ind μA (λ s → P (λ _ f → s _ (f ∘ A→B))) P∙ (Pf ∘ A→B)

μ-iso : ∀ {A B} → (A ↔ B) → SumProp A → SumProp B
μ-iso A↔B = μ-view (_⟨$⟩_ (Inverse.to A↔B))

μ-view-preserve : ∀ {A B} (A→B : A → B)(B→A : B → A)(A≈B : id ≗ B→A ∘ A→B) f (μA : SumProp A) → sum μA f ≡ sum (μ-view A→B μA) (f ∘ B→A)
μ-view-preserve A→B B→A A≈B f μA = sum-ext μA (≡.cong f ∘ A≈B)

μ-iso-preserve : ∀ {A B} (A↔B : A ↔ B) f (μA : SumProp A) → sum μA f ≡ sum (μ-iso A↔B μA) (f ∘ _⟨$⟩_ (Inverse.from A↔B))
μ-iso-preserve A↔B f μA = μ-view-preserve (_⟨$⟩_ (Inverse.to A↔B)) (_⟨$⟩_ (Inverse.from A↔B))
                            (≡.sym ∘ Inverse.left-inverse-of A↔B) f μA

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec.NP as Vec using (Vec; tabulate; _++_) renaming (map to vmap; sum to vsum; foldr to vfoldr; foldr₁ to vfoldr₁)

vmsum : ∀ m {n} → let open Mon m in
                  Vec C n → C
vmsum m = vfoldr _ _∙_ ε
  where open Monoid m

vsgsum : ∀ sg {n} → let open Sgrp sg in
                    Vec C (suc n) → C
vsgsum sg = vfoldr₁ _∙_
  where open Sgrp sg

-- let's recall that: tabulate f ≗ vmap f (allFin n)

-- searchMonFin : ∀ n → SearchMon (Fin n)
-- searchMonFin n m f = vmsum m (tabulate f)

searchFinSuc : ∀ n → Search (Fin (suc n))
searchFinSuc n _∙_ f = vfoldr₁ _∙_ (tabulate f)

μMaybe : ∀ {A} → SumProp A → SumProp (Maybe A)
μMaybe μA = μ-iso (FI.sym Maybe↔⊤⊎) (μ⊤ +μ μA)

μMaybe^ : ∀ {A} n → SumProp A → SumProp (Maybe^ n A)
μMaybe^ zero    μA = μA
μMaybe^ (suc n) μA = μMaybe (μMaybe^ n μA)

μFinSuc : ∀ n → SumProp (Fin (suc n))
μFinSuc n = searchFinSuc n , ind n
  where ind : ∀ n → SearchInd (searchFinSuc n)
        ind zero    P P∙ Pf = Pf zero
        ind (suc n) P P∙ Pf = P∙ (Pf zero) (ind n (λ s → P (λ op f → s op (f ∘ suc))) P∙ (Pf ∘ suc))

μFinSucIso : ∀ n → SumProp (Fin (suc n))
μFinSucIso n = μ-iso (Maybe^⊤↔Fin1+ n) (μMaybe^ n μ⊤)

μ^ : ∀ {A} (μA : SumProp A) n → SumProp (A ^ n)
μ^ μA zero    = μLift⊤
μ^ μA (suc n) = μA ×μ μ^ μA n

μVec : ∀ {A} (μA : SumProp A) n  → SumProp (Vec A n)
μVec μA n = μ-iso (^↔Vec n) (μ^ μA n)

searchVec : ∀ {A} n → Search A → Search (Vec A n)
searchVec zero    searchᴬ op f = f []
searchVec (suc n) searchᴬ op f = searchᴬ op (λ x → searchVec n searchᴬ op (f ∘ _∷_ x))

searchVec-spec : ∀ {A} (μA : SumProp A) n → searchVec n (search μA) ≈Search search (μVec μA n)
searchVec-spec μA zero    op f = ≡.refl
searchVec-spec μA (suc n) op f = search-ext μA op (λ x → searchVec-spec μA n op (f ∘ _∷_ x))

searchVec-++ : ∀ {A} n {m} (μA : SumProp A) sg
               → let open Sgrp sg in
                 (f : Vec A (n + m) → C)
               → search (μVec μA (n + m)) _∙_ f
               ≈ search (μVec μA n) _∙_ (λ xs →
                   search (μVec μA m) _∙_ (λ ys →
                     f (xs ++ ys)))
searchVec-++ zero    μA sg f = Sgrp.refl sg
searchVec-++ (suc n) μA sg f = search-sg-ext μA sg (λ x →
                                 searchVec-++ n μA sg (f ∘ _∷_ x))

sumVec-swap : ∀ {A} n {m} (μA : SumProp A)(f : Vec A (n + m) → ℕ)
            → sum (μVec μA n) (λ xs → sum (μVec μA m) (λ ys → f (xs ++ ys)))
            ≡ sum (μVec μA m) (λ ys → sum (μVec μA n) (λ xs → f (xs ++ ys)))
sumVec-swap n {m} μA f = sum-swap (μVec μA n) (μVec μA m) (λ xs ys → f (xs ++ ys))

swapS : ∀ {A B} → SumProp (A × B) → SumProp (B × A)
swapS = μ-iso swap-iso

swapS-preserve : ∀ {A B} f (μA×B : SumProp (A × B)) → sum μA×B f ≡ sum (swapS μA×B) (f ∘ swap)
swapS-preserve = μ-iso-preserve swap-iso

module _ {A : Set}(μA : SumProp A) where

  private
    sA = search μA

  extend : ∀ {n} → A → (Fin n → A) → Fin (suc n) → A
  extend x g zero    = x
  extend x g (suc i) = g i

  abs : Fin 0 → A
  abs ()

  -- There is one function Fin 0 → A (called abs) so this should be fine
  -- if not there is a version below that forces the domain to be non-empty
  sFun : ∀ n → Search (Fin n → A)
  sFun zero    op f = f abs
  sFun (suc n) op f = sA op (λ x → sFun n op (f ∘ extend x))

  Ind : ∀ n → SearchInd (sFun n)
  Ind zero    P P∙ Pf = Pf abs
  Ind (suc n) P P∙ Pf = 
    search-ind μA (λ sa → P (λ op f → sa op (λ x → sFun n op (f ∘ extend x)))) 
      P∙ 
      (λ x → Ind n (λ sf → P (λ op f → sf op (f ∘ extend x))) 
        P∙ (Pf ∘ extend x))

  μFun : ∀ {n} → SumProp (Fin n → A)
  μFun = sFun _ , Ind _

{-
  -- If we want to force non-empty domain

  sFun : ∀ n → Search (Fin (suc n) → A)
  sFun zero    op f = sA op (f ∘ const)
  sFun (suc n) op f = sA op (λ x → sFun n op (f ∘ extend x))

  Ind : ∀ n → SearchInd (sFun n)
  Ind zero    P P∙ Pf = search-ind μA (λ sa → P (λ op f → sa op (f ∘ const))) P∙ (Pf ∘ const)
  Ind (suc n) P P∙ Pf = search-ind μA (λ sa → P (λ op f → sa op (λ x → sFun n op (f ∘ extend x)))) 
      P∙ 
      (λ x → Ind n (λ sf → P (λ op f → sf op (f ∘ extend x))) P∙ (Pf ∘ extend x))

-}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
