{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Function.NP
open import Function.Extensionality
open import Data.Nat.NP hiding (_+_; _==_; pred) renaming (_*_ to _*ℕ_)
open import Data.Vec.NP hiding (sum)
open import Data.Maybe.NP
open import Data.One using (𝟙)
open import Data.Two hiding (_==_; _²)
open import Data.Fin.NP as Fin hiding (_+_; _-_; _≤_; pred)
open import Data.Product.NP
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP hiding (J)
open import Algebra.Field

module forking-lemma {{_ : FunExt}} where

open Indexed
  renaming (_∧°_ to _∩_; _∨°_ to _∪_; not° to ~_)

_>=1 : ∀ {n}(x : Fin n) → 𝟚
zero  >=1 = 0₂
suc x >=1 = 1₂

zero' : ∀ {n}{{n>0 : n > 0}} → Fin n
zero' {{s≤s _}} = zero

pred : ∀ {n}{{n>0 : n > 0}}(x : Fin (1+ n)) → Fin n
pred zero    = zero'
pred (suc x) = x

replace : ∀ {A : Type} {q} (I : Fin q)
            (hs hs' : Vec A q) → Vec A q
replace zero         hs       hs'  = hs'
replace (suc I) (h ∷ hs) (_ ∷ hs') = h ∷ replace I hs hs'

test-replace : replace (suc zero) (40 ∷ 41 ∷ 42 ∷ []) (60 ∷ 61 ∷ 62 ∷ []) ≡ 40 ∷ 61 ∷ 62 ∷ []
test-replace = refl

≡-prefix : ∀ {A : Type} {q} (I : Fin (suc q))
             (v₀ v₁ : Vec A q) → Type
≡-prefix zero    _         _         = 𝟙
≡-prefix (suc I) (x₀ ∷ v₀) (x₁ ∷ v₁) = (x₀ ≡ x₁) × ≡-prefix I v₀ v₁

≡-prefix (suc ()) [] []

postulate
  -- Pub    : Type
  Res    : Type -- Side output
  {-RndIG  : Type-}

  -- IG : RndIG → Pub

  q     : ℕ

  instance
    q≥1 : q ≥ 1

  #h     : ℕ

  instance
    #h≥2 : #h ≥ 2

  #ρ : ℕ
  instance
    #ρ≥1 : #ρ ≥ 1

RndAdv : Type -- Coin
RndAdv = Fin #ρ

H : Type
H = Fin #h

Adv = {-(x : Pub)-}(hs : Vec H q)(ρ : RndAdv) → Fin (suc q) × Res

postulate
  A : Adv
-- A x hs ρ
-- A x hs = ρ ←$ ...H ; A x hs ρ

-- IO : Type → Type
-- print : String → IO ()
-- #r : ℕ
-- #r≥1 : #r ≥ 1
-- Rnd = Fin #r
-- random : IO Rnd
-- run : (A : Input → Rnd → Res) → Input → IO Res
-- run A i = do r ← random
--              return (A i r)

-- Not used yet
well-def : Adv → Type
well-def A =
  ∀ {-x-} hs ρ →
    case A {-x-} hs ρ of λ { (I , σ) →
    ∀ hs' → ≡-prefix I hs hs' →  A {-x-} hs' ρ ≡ (I , σ) }

record Ω : Type where
  field
    -- rIG : RndIG
    hs hs' : Vec H q
    ρ      : RndAdv

Event = Ω → 𝟚

#Ω = ((#h ^ q) ^2) *ℕ #ρ
-- Ω ≃ Fin #Ω

-- #Ω ≡ countΩ λ _ → 1₁

{-
instance
  #Ω≥1 : #Ω ≥ 1
  #Ω≥1 = {!!}
-}

frk : Ω → Maybe (Res × Res)
frk r = case cond
        0: nothing
        1: just (σ , σ')
  module frk where
    open Ω r
    res  = A hs ρ
    I    = fst res
    σ    = snd res
    I-1  = pred I

    res' = A (replace I-1 hs hs') ρ
    I'   = fst res'
    σ'   = snd res'
    h    = hs  ‼ I-1
    h'   = hs' ‼ I-1
    I=I' = I == I'
    h=h' = h == h'
    h≢h' = not h=h'
    I≥1  = I >=1

    cond = I≥1 ∧ I=I' ∧ h≢h'

open frk

{-
==-refl : ∀ {n}(x : Fin n) → (x == x) ≡ 1₂
==-refl x = {!!}
-}

I-1= I=1+ I'=1+ : (i : Fin q) → Event
I-1=  i r = I-1 r == i
I=1+  i r = I   r == suc i
I'=1+ i r = I'  r == suc i

postulate
  baar : ∀ (I I' : Fin (suc q)) i → pred I == i ∧ I >=1 ∧ I == I' ≡ I' == suc i ∧ pred I == i
--baar I I' i = {!!}
-- either I ≡ I':
--   pred I == i ∧ I >=1 ≡ I == suc i ∧ pred I == i
-- or I ≢ I':
--  where open ≡-Reasoning

-- Acceptance event for A
acc : Event
acc = I≥1

Frk : Event
Frk = is-just ∘ frk

frk-cond : ∀ r → is-just (frk r) ≡ cond r
frk-cond r with cond r
... | 0₂ = refl
... | 1₂ = refl

instance
    #h≥1 : #h ≥ 1
    #h≥1 = ℕ≤.trans (s≤s z≤n) #h≥2

infix 0 _≥'_
infixr 2 _≥⟨_⟩_ _≡⟨_⟩_ _≡⟨by-definition⟩_
infix 2 _∎

postulate
  -- [0,1] : Type
  ℝ : Type
  ℝ-fld : Field ℝ

module ℝ = Field ℝ-fld
  renaming (ℕ[_] to ℕ▹ℝ)
  hiding (pred; suc)

open ℝ

postulate
  {- ≥ on ℝ, reflexive and transitive -}
  _≥'_ : ℝ → ℝ → Type
  _∎ : ∀ x → x ≥' x
  _≥⟨_⟩_ : ∀ x {y} → x ≥' y → ∀ {z} → y ≥' z → x ≥' z

_≡⟨_⟩_ : ∀ x {y} → x ≡ y → ∀ {z} → y ≥' z → x ≥' z
_ ≡⟨ refl ⟩ p = p

_≡⟨by-definition⟩_ : ∀ x {z} → x ≥' z → x ≥' z
_ ≡⟨by-definition⟩ p = p

import Explore.Fin
module Finᵉ = Explore.Fin.Regular

abstract
  sumFin : (n : ℕ)(f : Fin n → ℝ) → ℝ
  sumFin n = Finᵉ.explore n 0# _+_

{-
  sumVecH : (n : ℕ)(f : Vec H n → ℝ) → ℝ
-}

postulate
  sumΩ : (f : Ω → ℝ) → ℝ
{-
abstract
  sumΩ f = sumVecH q λ hs → sumVecH q λ hs' → sumFin #ρ λ ρ → f record { hs = hs; hs' = hs'; ρ = ρ }

  sumΩ-spec : ∀ f → sumΩ f ≡ sumVecH q λ hs → sumVecH q λ hs' → sumFin #ρ λ ρ → f record { hs = hs; hs' = hs'; ρ = ρ }
  sumΩ-spec f = refl
-}

𝟚▹ℝ : 𝟚 → ℝ
𝟚▹ℝ 0₂ = 0#
𝟚▹ℝ 1₂ = 1#

countΩ : Event → ℝ
countΩ A = sumΩ λ r → 𝟚▹ℝ (A r)

countΩ= : ∀ {A B} → (∀ r → A r ≡ B r) → countΩ A ≡ countΩ B
countΩ= f = ap sumΩ (λ= (ap 𝟚▹ℝ ∘ f))

1° : Event
1° _ = 1₂

RndVar = Ω → ℝ

_²' : RndVar → RndVar
(X ²') r = (X r)²

-- Non-empty-event
record NEE (A : Event) : Type where
  constructor _,_
  field
    r  : Ω
    Ar : A r ≡ 1₂

dummy-H : H
dummy-H = zero'
dummy-ρ : RndAdv
dummy-ρ = zero'
dummy-r : Ω
dummy-r = record { hs = replicate dummy-H ; hs' = replicate dummy-H ; ρ = dummy-ρ }

instance
  nee1 : NEE 1°
  nee1 = dummy-r , refl

{-
  nee-count : ∀{A}{{_ : NEE A}} → countΩ A ≥' 1#
  nee-count = {!!}
-}
lem-pred : ∀ {n}(x : Fin (1+ n))(y : Fin n){{n>0 : n > 0}} → x ≡ suc y → pred x ≡ y
lem-pred .(suc y) y refl = refl

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

infix 7 _/#Ω _/#h _/q

_/#Ω : ℝ → ℝ
x /#Ω = x / ℕ▹ℝ #Ω

_/#h : ℝ → ℝ
x /#h = x / ℕ▹ℝ #h

_/q : ℝ → ℝ
x /q = x / ℕ▹ℝ q

postulate
  Pr[_∥_] : (A B : Event){{_ : NEE B}} → ℝ
--Pr[ A ∥ B ] = {!!} -- countΩ (λ r → A r ∧ B r) / countΩ B -- OR: countΩ A / (#Ω - countΩ B)

Pr[_] : Event → ℝ
Pr[ A ] = countΩ A /#Ω

postulate
  Pr[_∥1]-spec : ∀ A → Pr[ A ∥ 1° ] ≡ Pr[ A ]

Pr= : ∀ {A B : Event} → (∀ r → A r ≡ B r) → Pr[ A ] ≡ Pr[ B ]
Pr= f = ap _/#Ω (countΩ= f)

postulate
  Pr[A∩B∩~C] : ∀ A B C → Pr[ A ∩ B ∩ ~ C ] ≥' Pr[ A ∩ B ] − Pr[ A ∩ C ]
--Pr[A∩B∩~C] A B C = {!!}

{-
postulate
  integral : (ℝ⁺ → ℝ) → ℝ
-}

postulate
  E[_] : RndVar → ℝ
--E[ X ] = integral (λ x → Pr[ X ≥° x ])

postulate
  lemma2 : ∀ X → E[ X ²' ] ≥' E[ X ] ²

postulate
  conditional : ∀ A B {{_ : NEE B}} → Pr[ A ∩ B ] ≡ Pr[ A ∥ B ] * Pr[ B ]

  sumPr : ∀ {n}(I : Ω → Fin n)(A : Event)
          → (sumFin n λ i → Pr[ (λ r → I r == i) ∩ A ]) ≡ Pr[ A ]

{-
lem-NEE-pred' : ∀ {n}(X : Ω → Fin (1+ n))(y : Fin n){{n>0 : n > 0}} → NEE (λ r → X r == suc y) → NEE (λ r → pred (X r) == y)
lem-NEE-pred' = {!!}

lem-NEE-pred : ∀ {n} (X : Ω → Fin (1+ n)) (x : Fin n){{n>0 : n > 0}} → NEE (λ r → pred (X r) == x)
lem-NEE-pred X x = {!!} , {!!}
-}

instance
  postulate
    -- NOT sure it's actually true
    nee-I=1+ : {i : Fin q} → NEE (I-1= i)
  --nee-I=1+ {i} = lem-NEE-pred I i

lemma1-5 : Pr[ I≥1 ∩ h=h' ] ≡ Pr[ I≥1 ] /#h
lemma1-5 = {!!}

-- Lemma 1, equation (3)
lemma1-3 : Pr[ Frk ] ≥' Pr[ acc ] * ((Pr[ acc ] /q) − (1# /#h))
lemma1-3 = Pr[ Frk ]
       ≡⟨ Pr= frk-cond ⟩
         Pr[ I≥1 ∩ I=I' ∩ h≢h' ]
       ≥⟨ Pr[A∩B∩~C] I≥1 I=I' h=h' ⟩
         Pr[ I≥1 ∩ I=I' ] − Pr[ I≥1 ∩ h=h' ]
       ≡⟨ ap (λ x → Pr[ I≥1 ∩ I=I' ] − x) lemma1-5 ⟩
         Pr[ I≥1 ∩ I=I' ] − (Pr[ I≥1 ] /#h)
       ≡⟨by-definition⟩
         Pr[ I≥1 ∩ I=I' ] − (Pr[ acc ] /#h)
       ≡⟨ {!!} ⟩
         Pr[ acc ] * ((Pr[ acc ] /q) − (1# /#h))
       ∎

lemma1-4 : Pr[ I≥1 ∩ I=I' ] ≥' Pr[ acc ] ² /q
lemma1-4
  = Pr[ I≥1 ∩ I=I' ]
  ≡⟨ ! sumPr I-1 (I≥1 ∩ I=I') ⟩
    sumFin q (λ i → Pr[ I-1= i ∩ I≥1 ∩ I=I' ])
  ≡⟨ ap (sumFin q) (λ= (λ i → Pr= (λ r → baar (I r) (I' r) i))) ⟩
    sumFin q (λ i → Pr[ I'=1+ i ∩ I-1= i ])
  ≡⟨ ap (sumFin q) (λ= (λ i → conditional (I'=1+ i) (I-1= i))) ⟩
    sumFin q (λ i → Pr[ I'=1+ i ∥ I-1= i ] * Pr[ I-1= i ])
  ≡⟨ {!!} ⟩
    Pr[ acc ] ² /q
  ∎

-- -}
-- -}
-- -}
-- -}
-- -}
