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
open import Search.Derived

module sum where

_≈Sum_ : ∀ {A} → (sum₀ sum₁ : Sum A) → ★ _
sum₀ ≈Sum sum₁ = ∀ f → sum₀ f ≡ sum₁ f

_≈Search_ : ∀ {A} → (s₀ s₁ : Search _ A) → ★₁
s₀ ≈Search s₁ = ∀ {B} (op : Op₂ B) f → s₀ op f ≡ s₁ op f

μ-iso : ∀ {A B} → (A ↔ B) → Searchable A → Searchable B
μ-iso {A}{B} A↔B μA = mk searchᴮ ind ade
  where
    A→B = to A↔B

    searchᴮ : Search _ B
    searchᴮ m f = search μA m (f ∘ A→B)

    sumᴮ = searchᴮ _+_

    ind : SearchInd _ searchᴮ
    ind P P∙ Pf = search-ind μA (λ s → P (λ _ f → s _ (f ∘ A→B))) P∙ (Pf ∘ A→B)

    ade : AdequateSum sumᴮ
    ade f = sym-first-iso A↔B FI.∘ adequate-sum μA (f ∘ A→B)

-- I guess this could be more general
μ-iso-preserve : ∀ {A B} (A↔B : A ↔ B) f (μA : Searchable A) → sum μA f ≡ sum (μ-iso A↔B μA) (f ∘ from A↔B)
μ-iso-preserve A↔B f μA = sum-ext μA (≡.cong f ∘ ≡.sym ∘ Inverse.left-inverse-of A↔B)

μLift : ∀ {A} → Searchable A → Searchable (Lift A)
μLift = μ-iso (FI.sym Lift↔id)

μ⊤ : Searchable ⊤
μ⊤ = mk _ ind ade
  where
    srch : Search _ ⊤
    srch _ f = f _

    ind : SearchInd _ srch
    ind _ _ Pf = Pf _

    ade : AdequateSum (srch _+_)
    ade x = FI.sym ⊤×A↔A

searchBit : ∀ {m} → Search m Bit
searchBit _∙_ f = f 0b ∙ f 1b

searchBit-ind : ∀ {m p} → SearchInd p {m} searchBit
searchBit-ind _ _P∙_ Pf = Pf 0b P∙ Pf 1b

μBit : Searchable Bit
μBit = μ-iso (FI.sym Bit↔⊤⊎⊤) (μ⊤ ⊎-μ μ⊤)

focusBit : ∀ {a} → Focus {a} searchBit
focusBit (false , x) = inj₁ x
focusBit (true ,  x) = inj₂ x

focusedBit : Focused {L.zero} searchBit
focusedBit {B} = inverses focusBit unfocus (⇒) (⇐)
  where open Searchable₁₁ searchBit-ind
        ⇒ : (x : Σ Bit B) → _
        ⇒ (false , x) = ≡.refl
        ⇒ (true  , x) = ≡.refl
        ⇐ : (x : B 0b ⊎ B 1b) → _
        ⇐ (inj₁ x) = ≡.refl
        ⇐ (inj₂ x) = ≡.refl

lookupBit : ∀ {a} → Lookup {a} searchBit
lookupBit = proj

_⊎'_ : ★₀ → ★₀ → ★₀
A ⊎' B = Σ Bool (cond A B)

_μ⊎'_ : ∀ {A B} → Searchable A → Searchable B → Searchable (A ⊎' B)
μA μ⊎' μB = μΣ μBit (λ { {true} → μA ; {false} → μB })

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

μΠ⊎⁻ : ∀ {A B}{C : A ⊎ B → ★ _} → Searchable (Π A (C ∘ inj₁) × Π B (C ∘ inj₂))
     → Searchable (Π (A ⊎ B) C)
μΠ⊎⁻ = μ-iso {!!}

_⊎-Fun_ : ∀ {A B} → Funable A → Funable B → Funable (A ⊎ B)
_⊎-Fun_ (μA , μA→) (μB , μB→) = (μA ⊎-μ μB) , (λ X → μΠ⊎⁻ (μA→ X ×-μ μB→ X))

S⊤ : ∀ {m A} → Search m A → Search m (⊤ → A)
S⊤ sA _∙_ f = sA _∙_ (f ∘ const)

SΠBit : ∀ {m A} → Search m (A 0b) → Search m (A 1b)
                → Search m (Π Bit A)
SΠBit sA₀ sA₁ _∙_ f = sA₀ _∙_ λ x → sA₁ _∙_ λ y → f λ {true → y; false → x}

sum-const : ∀ {A} (μA : Searchable A) → ∀ k → sum μA (const k) ≡ Card μA * k
sum-const μA k
  rewrite ℕ°.*-comm (Card μA) k
        | ≡.sym (sum-lin μA (const 1) k)
        | proj₂ ℕ°.*-identity k = ≡.refl

infixr 4 _×Sum-proj₁_ _×Sum-proj₁'_ _×Sum-proj₂_ _×Sum-proj₂'_

_×Sum-proj₁_ : ∀ {A B}
                 (μA : Searchable A)
                 (μB : Searchable B)
                 f →
                 sum (μA ×-μ μB) (f ∘ proj₁) ≡ Card μB * sum μA f
(μA ×Sum-proj₁ μB) f
  rewrite sum-ext μA (sum-const μB ∘ f)
        = sum-lin μA f (Card μB)

_×Sum-proj₂_ : ∀ {A B}
                 (μA : Searchable A)
                 (μB : Searchable B)
                 f →
                 sum (μA ×-μ μB) (f ∘ proj₂) ≡ Card μA * sum μB f
(μA ×Sum-proj₂ μB) f = sum-const μA (sum μB f)

_×Sum-proj₁'_ : ∀ {A B}
                  (μA : Searchable A) (μB : Searchable B)
                  {f} {g} →
                  sum μA f ≡ sum μA g →
                  sum (μA ×-μ μB) (f ∘ proj₁) ≡ sum (μA ×-μ μB) (g ∘ proj₁)
(μA ×Sum-proj₁' μB) {f} {g} sumf≡sumg
  rewrite (μA ×Sum-proj₁ μB) f
        | (μA ×Sum-proj₁ μB) g
        | sumf≡sumg = ≡.refl

_×Sum-proj₂'_ : ∀ {A B}
                  (μA : Searchable A) (μB : Searchable B)
                  {f} {g} →
                  sum μB f ≡ sum μB g →
                  sum (μA ×-μ μB) (f ∘ proj₂) ≡ sum (μA ×-μ μB) (g ∘ proj₂)
(μA ×Sum-proj₂' μB) sumf≡sumg = sum-ext μA (const sumf≡sumg)

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

μMaybe : ∀ {A} → Searchable A → Searchable (Maybe A)
μMaybe μA = μ-iso (FI.sym Maybe↔⊤⊎) (μ⊤ ⊎-μ μA)

μMaybe^ : ∀ {A} n → Searchable A → Searchable (Maybe^ n A)
μMaybe^ zero    μA = μA
μMaybe^ (suc n) μA = μMaybe (μMaybe^ n μA)

{-
μFinSuc : ∀ n → Searchable (Fin (suc n))
μFinSuc n = mk _ (ind n) {!!}
  where ind : ∀ n → SearchInd _ (searchFinSuc n)
        ind zero    P P∙ Pf = Pf zero
        ind (suc n) P P∙ Pf = P∙ (Pf zero) (ind n (λ s → P (λ op f → s op (f ∘ suc))) P∙ (Pf ∘ suc))
-}

μFinSuc : ∀ n → Searchable (Fin (suc n))
μFinSuc n = μ-iso (Maybe^⊤↔Fin1+ n) (μMaybe^ n μ⊤)

μ^ : ∀ {A} (μA : Searchable A) n → Searchable (A ^ n)
μ^ μA zero    = μLift μ⊤
μ^ μA (suc n) = μA ×-μ μ^ μA n

μVec : ∀ {A} (μA : Searchable A) n  → Searchable (Vec A n)
μVec μA n = μ-iso (^↔Vec n) (μ^ μA n)

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

swapS : ∀ {A B} → Searchable (A × B) → Searchable (B × A)
swapS = μ-iso swap-iso

swapS-preserve : ∀ {A B} f (μA×B : Searchable (A × B)) → sum μA×B f ≡ sum (swapS μA×B) (f ∘ swap)
swapS-preserve = μ-iso-preserve swap-iso

module _ {A : Set}(μA : Searchable A) where

  private
    sA = search μA

  extend : ∀ {n} → A → (Fin n → A) → Fin (suc n) → A
  extend x g zero    = x
  extend x g (suc i) = g i

  abs : Fin 0 → A
  abs ()

  -- There is one function Fin 0 → A (called abs) so this should be fine
  -- if not there is a version below that forces the domain to be non-empty
  sFun : ∀ n → Search _ (Fin n → A)
  sFun zero    op f = f abs
  sFun (suc n) op f = sA op (λ x → sFun n op (f ∘ extend x))

  ind : ∀ n → SearchInd _ (sFun n)
  ind zero    P P∙ Pf = Pf abs
  ind (suc n) P P∙ Pf =
    search-ind μA (λ sa → P (λ op f → sa op (λ x → sFun n op (f ∘ extend x))))
      P∙
      (λ x → ind n (λ sf → P (λ op f → sf op (f ∘ extend x)))
        P∙ (Pf ∘ extend x))

  μFun : ∀ {n} → Searchable (Fin n → A)
  μFun = mk _ (ind _) {!!}

module BigDistr
  {A}(μA : Searchable A)
  (cm       : CommutativeMonoid L.zero L.zero)
  -- we want (open CMon cm) !!!
  (_◎_      : let open CMon cm in C  → C → C)
  (distrib  : let open CMon cm in _DistributesOver_ _≈_ _◎_ _∙_)
  (_◎-cong_ : let open CMon cm in _◎_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_) where

  open CMon cm

  μF→A = μFun μA

  -- Sum over A
  Σᴬ = search μA _∙_

  -- Sum over (Fin(1+I)→A) functions
  Σ' : ∀ {I} → ((Fin (suc I) → A) → C) → C
  Σ' = search μF→A _∙_

  -- Product over Fin(1+I) values
  Π' = λ I → search (μFinSuc I) _◎_

  bigDistr : ∀ I F → Π' I (Σᴬ ∘ F) ≈ Σ' (Π' I ∘ _ˢ_ F)
  bigDistr zero    _ = refl
  bigDistr (suc I) F
    = Σᴬ (F zero) ◎ Π' I (Σᴬ ∘ F ∘ suc)
    ≈⟨ refl ◎-cong bigDistr I (F ∘ suc) ⟩
      Σᴬ (F zero) ◎ Σ' (Π' I ∘ _ˢ_ (F ∘ suc))
    ≈⟨ sym (search-linʳ μA monoid _◎_ (F zero) (Σ' (Π' I ∘ _ˢ_ (F ∘ suc))) (proj₂ distrib)) ⟩
      Σᴬ (λ j → F zero j ◎ Σ' (Π' I ∘ _ˢ_ (F ∘ suc)))
    ≈⟨ search-sg-ext μA semigroup (λ j → sym (search-linˡ μF→A monoid _◎_ (Π' I ∘ _ˢ_ (F ∘ suc)) (F zero j) (proj₁ distrib))) ⟩
      (Σᴬ λ j → Σ' λ f → F zero j ◎ Π' I ((F ∘ suc) ˢ f))
    ∎

FinDist : ∀ {n} → DistFun (μFinSuc n) (λ μX → μFun μX)
FinDist μB c ◎ distrib ◎-cong f = BigDistr.bigDistr μB c ◎ distrib ◎-cong _ f

simple : ∀ {A : Set}{P : A → A → Set} → (∀ x → P x x) → {x y : A} → x ≡ y → P x y
simple r ≡.refl = r _

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

⊎-Dist : ∀ {A B} FA FB → DistFunable {A} FA → DistFunable {B} FB → DistFunable (FA ⊎-Fun FB)
⊎-Dist FA FB FA-dist FB-dist μX c _◎_ distrib _◎-cong_ f
 = Πᴬ (Σ' ∘ f ∘ inj₁) ◎ Πᴮ (Σ' ∘ f ∘ inj₂)
 ≈⟨ FA-dist μX c _◎_ distrib _◎-cong_ (f ∘ inj₁) ◎-cong FB-dist μX c _◎_ distrib _◎-cong_ (f ∘ inj₂) ⟩
   Σᴬ (λ fa → Πᴬ (λ i → f (inj₁ i) (fa i))) ◎ Σᴮ (λ fb → Πᴮ (λ i → f (inj₂ i) (fb i)))
 ≈⟨ sym (search-linʳ (negative FA μX) monoid _◎_ _ _ (proj₂ distrib)) ⟩
   Σᴬ (λ fa → Πᴬ (λ i → f (inj₁ i) (fa i)) ◎ Σᴮ (λ fb → Πᴮ (λ i → f (inj₂ i) (fb i))))
 ≈⟨ search-sg-ext (negative FA μX) semigroup (λ fa → sym (search-linˡ (negative FB μX) monoid _◎_ _ _ (proj₁ distrib))) ⟩
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


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
