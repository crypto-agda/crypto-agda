{-# OPTIONS --without-K #-}
open import Type using (Type; Type₁)
open import Function.NP renaming (const to `_)
open import Function.Extensionality
open import Data.Nat.NP hiding (_+_; _==_; pred) renaming (_*_ to _*ℕ_)
open import Data.Vec.NP hiding (sum)
open import Data.Maybe.NP
open import Data.One using (𝟙)
open import Data.Two hiding (_²) renaming (_==_ to _==𝟚_)
open import Data.Fin.NP as Fin hiding (_+_; _-_; _≤_; pred)
open import Data.Product.NP
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP hiding (J; _≗_)
open import Algebra.Field
open import HoTT
open Equivalences

module probas {{_ : FunExt}} (Ω : Type)(dummy-r : Ω) where

open Indexed
  renaming (_∧°_ to _∩_; _∨°_ to _∪_; not° to ~_) -- ; _==°_ to _≗_)

Event = Ω → 𝟚

infix 0 _≥'_

postulate
  -- [0,1] : Type
  ℝ : Type
  ℝ-fld : Field ℝ

module ℝ = Field ℝ-fld
  renaming (ℕ[_] to ℕ▹ℝ)
  hiding (pred; suc)

open ℝ public

1/_ : ℕ → ℝ
1/ x = (ℕ▹ℝ x)⁻¹

postulate
  {- ≥ on ℝ, reflexive and transitive -}
  _≥'_ : ℝ → ℝ → Type

  −-mono : ∀ {x y z} → x ≥' y → x − z ≥' y − z

module ≥'-Reasoning where
  infixr 2 _≥⟨_⟩_ _≡⟨_⟩_ _≡⟨by-definition⟩_
  infix 2 _∎
  postulate
    _∎ : ∀ x → x ≥' x
    _≥⟨_⟩_ : ∀ x {y} → x ≥' y → ∀ {z} → y ≥' z → x ≥' z

  _≡⟨_⟩_ : ∀ x {y} → x ≡ y → ∀ {z} → y ≥' z → x ≥' z
  _ ≡⟨ refl ⟩ p = p

  _≡⟨by-definition⟩_ : ∀ x {z} → x ≥' z → x ≥' z
  _ ≡⟨by-definition⟩ p = p

infixr 7 _≗_

_≗_ : ∀ {n}{A : Type}(f g : A → Fin n) → A → 𝟚
(f ≗ g) a = f a == g a

record _∈[0,1] (x : ℝ) : Type where
  field
    ≥0 : x ≥' 0#
    ≤1 : 1# ≥' x


import Explore.Fin
module Finᵉ = Explore.Fin.Regular

abstract
  sumFin : (n : ℕ)(f : Fin n → ℝ) → ℝ
  sumFin n = Finᵉ.explore n 0# _+_

  sumFin= : ∀ {n}{f g : Fin n → ℝ}→ (∀ r → f r ≡ g r) → sumFin n f ≡ sumFin n g
  sumFin= = Finᵉ.explore-ext _ 0# _+_

𝟚▹ℝ : 𝟚 → ℝ
𝟚▹ℝ 0₂ = 0#
𝟚▹ℝ 1₂ = 1#

postulate
  #Ω : ℕ
  sumΩ : (f : Ω → ℝ) → ℝ

countΩ : Event → ℝ
countΩ A = sumΩ λ r → 𝟚▹ℝ (A r)

countΩ= : ∀ {A B} → (∀ r → A r ≡ B r) → countΩ A ≡ countΩ B
countΩ= f = ap sumΩ (λ= (ap 𝟚▹ℝ ∘ f))

1° : Event
1° _ = 1₂

RndVar = Ω → ℝ

_²' : RndVar → RndVar
(X ²') r = (X r)²

infix 7 _/#Ω

_/#Ω : ℝ → ℝ
x /#Ω = x / ℕ▹ℝ #Ω

-- Non-empty-event
record NEE (A : Event) : Type where
  constructor _,_
  field
    r  : Ω
    Ar : A r ≡ 1₂

{-
_⊃_ : (A B : Event) → Event
A ⊃ B = (~ A) ∪ B

∀° : Event → Type
∀° A = ∀ r → A r ≡ 1₂
-}

_⊃_ : (A B : Event) → Type
A ⊃ B = ∀ r → A r ≡ 1₂ → B r ≡ 1₂

NEE-⊃ : (A B : Event) → A ⊃ B → NEE A → NEE B
NEE-⊃ A B i (r , p) = r , i r p

postulate
  Pr[_∥_] : (A B : Event){{_ : NEE B}} → ℝ
--Pr[ A ∥ B ] = {!!} -- countΩ (λ r → A r ∧ B r) / countΩ B -- OR: countΩ A / (#Ω - countΩ B)

Pr[_] : Event → ℝ
Pr[ A ] = countΩ A /#Ω

instance
  nee1 : NEE 1°
  nee1 = dummy-r , refl

postulate
  Pr[_∥1]-spec : ∀ A → Pr[ A ∥ 1° ] ≡ Pr[ A ]

Pr= : ∀ {A B : Event} → (∀ r → A r ≡ B r) → Pr[ A ] ≡ Pr[ B ]
Pr= f = ap _/#Ω (countΩ= f)

record IndepFun {O : Type} (A B : Ω → O) : Type₁ where
  field
    Ω0 Ω1 : Type
    α0 : Ω → Ω0
    α1 : Ω → Ω1
    α≃ : Is-equiv < α0 , α1 >
    A0 : Ω0 → O
    B1 : Ω1 → O
    A≃ : A ≡ A0 ∘ α0
    B≃ : B ≡ B1 ∘ α1

-- irrefl : ∀ f → ¬(IndepFun f f)

Surjective : {A B : Type}(f : A → B) → Type
Surjective {A} {B} f = ∃ λ (g : B → A) → (f ∘ g) ∼ id

postulate
  countΩ-== : ∀ (A B : Event) → countΩ (λ r → A r ==𝟚 B r) ≡ 1#

  Pr-surj : ∀{n}(f : Ω → Fin n) k → Surjective f → Pr[ (λ r → f r == k) ] ≡ 1/ n

  Pr-indep : ∀{n}(f g : Ω → Fin n) → Surjective f → Surjective g → IndepFun f g → Pr[ (λ r → f r == g r) ] ≡ 1/ n

{-
  Pr[ (λ r → f r == g r) ]
  ≡
  sumΩ (λ r → f r == g r) / #Ω
  ≡
  sumΩ (λ r → A0 (α0 r) == B1 (α1 r)) / #Ω
  ≡
  sum(Ω0×Ω1) (λ (r0 , r1) → A0 r0 == B1 r1) / #Ω
  ≡
  sumΩ0 (λ r0 → sumΩ1 λ r1 → A0 r0 == B1 r1) / #Ω
  ...
  ≡
  1/n
-}

postulate
  Pr[A∩B∩~C] : ∀ A B C → Pr[ A ∩ B ∩ ~ C ] ≥' Pr[ A ∩ B ] − Pr[ A ∩ C ]
--Pr[A∩B∩~C] A B C = {!!}

  Indep : (A B : Event) → Type₁

  Pr-∩-*-indep : ∀ A B → Indep A B → Pr[ A ∩ B ] ≡ Pr[ A ] * Pr[ B ]


{-
postulate
  integral : (ℝ⁺ → ℝ) → ℝ
-}

  E[_] : RndVar → ℝ
--E[ X ] = integral (λ x → Pr[ X ≥° x ])

  lemma2 : ∀ X → E[ X ²' ] ≥' E[ X ] ²
  -- lemma3' : {q : ℕ}(xs : Vec ℝ q) → sumFin q (λ i → (xs ‼ i)²) ≥' (sumFin q λ i → xs ‼ i)² / ℕ▹ℝ q
  lemma3 : {q : ℕ}(xs : Fin q → ℝ) → sumFin q (λ i → (xs i)²) ≥' (sumFin q λ i → xs i)² / ℕ▹ℝ q

  conditional : ∀ A B {{_ : NEE B}} → Pr[ A ∩ B ] ≡ Pr[ A ∥ B ] * Pr[ B ]

  sumPr : ∀ {n}(I : Ω → Fin n)(A : Event)
          → (sumFin n λ i → Pr[ I ≗ ` i ∩ A ]) ≡ Pr[ A ]

  _==Ω_ : (r₀ r₁ : Ω) → 𝟚

{-
infixr 7 _≗Ω_
_≗Ω_ : ∀ {A : Type}(f g : A → Ω) → A → 𝟚
(f ≗Ω g) a = f a ==Ω g a
-}

  E-spec' : ∀ X → E[ X ] ≡ sumΩ λ r → X r * Pr[ _==Ω_ r ]
  E-spec2 : ∀ X → E[ X ] ≡ sumΩ λ r → X r * (countΩ (λ r' → r ==Ω r') /#Ω)
  E-spec3 : ∀ X → E[ X ] ≡ sumΩ λ r → X r * (sumΩ (λ r' → 𝟚▹ℝ (r ==Ω r')) /#Ω)
  E-spec4 : ∀ X → E[ X ] ≡ (sumΩ λ r → X r * (sumΩ (λ r' → 𝟚▹ℝ (r ==Ω r')))) /#Ω

{-
sumΩ (λ r' → 𝟚▹ℝ (r ==Ω r'))
≡
1
-}

  E-spec5 : ∀ X → E[ X ] ≡ sumΩ (λ r → X r /#Ω)
  E-spec6 : ∀ X → E[ X ] ≡ sumΩ (λ r → X r) /#Ω

  sumΩ-lin : ∀ k f → sumΩ (λ r → f r * k) ≡ sumΩ f * k
  sumΩ≥ : ∀{f g : Ω → ℝ}→ (∀ r → f r ≥' g r) → sumΩ f ≥' sumΩ g

  sumFin≥ : ∀ {n}{f g : Fin n → ℝ}→ (∀ r → f r ≥' g r) → sumFin n f ≥' sumFin n g

  Pr∈[0,1] : ∀ A → Pr[ A ] ∈[0,1]
  ²-mono : ∀ {x} → x ∈[0,1] → x ≥' x ²
  *-mono : ∀ {x x' y y'} → x ≥' x' → y ≥' y' → (x * y) ≥' (x' * y')
-- -}
-- -}
-- -}
-- -}
