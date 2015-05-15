{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Function.NP renaming (const to `_)
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
open import Relation.Binary.PropositionalEquality.NP hiding (J; _≗_)
open import Algebra.Field

module forking-lemma {{_ : FunExt}} where

open Indexed
  renaming (_∧°_ to _∩_; _∨°_ to _∪_; not° to ~_) -- ; _==°_ to _≗_)

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

test-replace : replace (# 1) (40 ∷ 41 ∷ 42 ∷ []) (60 ∷ 61 ∷ 62 ∷ []) ≡ 40 ∷ 61 ∷ 62 ∷ []
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

instance
    #h≥1 : #h ≥ 1
    #h≥1 = ℕ≤.trans (s≤s z≤n) #h≥2

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
  constructor mk
  field
    -- rIG : RndIG
    hs hs' : Vec H q
    ρ      : RndAdv

dummy-H : H
dummy-H = zero'
dummy-ρ : RndAdv
dummy-ρ = zero'
dummy-r : Ω
dummy-r = record { hs = replicate dummy-H ; hs' = replicate dummy-H ; ρ = dummy-ρ }

open import probas Ω dummy-r

-- #Ω = ((#h ^ q) ^2) *ℕ #ρ

1/#Ω = (ℕ▹ℝ #Ω)⁻¹

-- Ω ≃ Fin #Ω

-- #Ω ≡ countΩ λ _ → 1₁

{-
instance
  #Ω≥1 : #Ω ≥ 1
  #Ω≥1 = {!!}
-}

module frk' (i : Fin q)(r : Ω) where
  open Ω r
  res' = A (replace i hs hs') ρ
  I'   = fst res'
  σ'   = snd res'
  h    = hs  ‼ i
  h'   = hs' ‼ i
  h=h' = h == h'
  h≢h' = not h=h'

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
    open frk' I-1 r public
    I≥1  = I >=1
    I=I' = I == I'
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

{-
fΩ : Fin q → Vec H q → Ω → Ω
fΩ i hs'' r = mk hs (replace i hs' hs'') ρ
  where
    open Ω r
-}

X-event : Fin q → Vec H q → RndAdv → Event
X-event i hs'' ρ r = fst (A (replace i r.hs' hs'') ρ) == suc i
  where module r = Ω r
-- X-event i hs'' ρ = frk'.I' i (mk {!!} hs'' ρ) {-(fΩ i hs'' r)-} == suc i
-- X-event i hs'' r = frk'.I' i (fΩ i hs'' r) == suc i

-- X-event ... ≡ I ...

X-pr : Fin q → Vec H q → RndAdv → ℝ
X-pr i hs'' ρ = Pr[ X-event i hs'' ρ ]

X : Fin q → RndVar
X i r = X-pr i hs ρ
  where open Ω r

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

frk-cond : ∀ r → Frk r ≡ cond r
frk-cond r with cond r
... | 0₂ = refl
... | 1₂ = refl
{-
  sumVecH : (n : ℕ)(f : Vec H n → ℝ) → ℝ
-}
{-
abstract
  sumΩ f = sumVecH q λ hs → sumVecH q λ hs' → sumFin #ρ λ ρ → f record { hs = hs; hs' = hs'; ρ = ρ }

  sumΩ-spec : ∀ f → sumΩ f ≡ sumVecH q λ hs → sumVecH q λ hs' → sumFin #ρ λ ρ → f record { hs = hs; hs' = hs'; ρ = ρ }
  sumΩ-spec f = refl
-}

infix 7 _/#h _/q

_/#h : ℝ → ℝ
x /#h = x / ℕ▹ℝ #h

_/q : ℝ → ℝ
x /q = x / ℕ▹ℝ q

1/#h = (ℕ▹ℝ #h)⁻¹

{-
  nee-count : ∀{A}{{_ : NEE A}} → countΩ A ≥' 1#
  nee-count = {!!}
-}
lem-pred : ∀ {n}(x : Fin (1+ n))(y : Fin n){{n>0 : n > 0}} → x ≡ suc y → pred x ≡ y
lem-pred .(suc y) y refl = refl
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

{-
I : Ω → Fin q
B ⊆ A
∃ r : Ω, I r == i, X-event i
I == i
sumFin q (λ i → E[ Pr[ X-event i ] ]) ≡ Pr[ I ≥1 ]
-}

postulate
  _==Ω_ : (r₀ r₁ : Ω) → 𝟚

{-
infixr 7 _≗Ω_
_≗Ω_ : ∀ {A : Type}(f g : A → Ω) → A → 𝟚
(f ≗Ω g) a = f a ==Ω g a
-}

postulate
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

lemma1-6 : sumFin q (λ i → E[ X i ]) ≡ Pr[ acc ]
lemma1-6 = {!!}

postulate
  sumFin≥ : ∀ {n}{f g : Fin n → ℝ}→ (∀ r → f r ≥' g r) → sumFin n f ≥' sumFin n g

lemma1-7 : ∀ i → Pr[ I-1= i ] ≡ sumΩ (X i)
lemma1-7 = {!!}

lemma1-8 : ∀ i → Pr[ I'=1+ i ∥ I-1= i ] ≡ 1/#Ω
lemma1-8 i = {!!}

record _∈[0,1] (x : ℝ) : Type where
  field
    ≥0 : x ≥' 0#
    ≤1 : 1# ≥' x

postulate
  Pr∈[0,1] : ∀ A → Pr[ A ] ∈[0,1]
  ²-mono : ∀ {x} → x ∈[0,1] → x ≥' x ²
  *-mono : ∀ {x x' y y'} → x ≥' x' → y ≥' y' → (x * y) ≥' (x' * y')

lemma1-4 : Pr[ I≥1 ∩ I=I' ] ≥' Pr[ acc ] ² /q
lemma1-4
  = Pr[ I≥1 ∩ I=I' ]
  ≡⟨ ! sumPr I-1 (I≥1 ∩ I=I') ⟩
    sumFin q (λ i → Pr[ I-1= i ∩ I≥1 ∩ I=I' ])
  ≡⟨ sumFin= (λ i → Pr= (λ r → baar (I r) (I' r) i)) ⟩
    sumFin q (λ i → Pr[ I'=1+ i ∩ I-1= i ])
  ≡⟨ sumFin= (λ i → conditional (I'=1+ i) (I-1= i)) ⟩
    sumFin q (λ i → Pr[ I'=1+ i ∥ I-1= i ] * Pr[ I-1= i ])
  ≡⟨ sumFin= (λ i → *= (lemma1-8 i) (lemma1-7 i)) ⟩
    sumFin q (λ i → 1/#Ω * sumΩ (X i))
  ≡⟨ sumFin= (λ i → *-comm) ⟩
    sumFin q (λ i → sumΩ (X i) /#Ω)
  ≡⟨ sumFin= (λ i → ! sumΩ-lin (ℕ▹ℝ #Ω ⁻¹) (X i)) ⟩
    sumFin q (λ i → sumΩ λ r → X i r /#Ω)
  ≥⟨ sumFin≥ (λ i → sumΩ≥ (λ r → *-mono (²-mono (Pr∈[0,1] (X-event i (Ω.hs r) (Ω.ρ r)))) (1/#Ω ∎))) ⟩
    sumFin q (λ i → sumΩ λ r → (X i r)² /#Ω)
  ≡⟨ sumFin= (λ i → ! E-spec5 (X i ²')) ⟩
    sumFin q (λ i → E[ X i ²' ])
  ≥⟨ sumFin≥ (λ i → lemma2 (X i)) ⟩
    sumFin q (λ i → (E[ X i ] ²))
  ≥⟨ lemma3 (λ i → E[ X i ]) ⟩
    (sumFin q λ i → E[ X i ])² /q
  ≡⟨ ap (λ z → z ² /q) lemma1-6 ⟩
    Pr[ acc ] ² /q
  ∎

-- Lemma 1, equation (3)
lemma1-3 : Pr[ Frk ] ≥' Pr[ acc ] * ((Pr[ acc ] /q) − (1/#h))
lemma1-3 = Pr[ Frk ]
  ≡⟨ Pr= frk-cond ⟩
    Pr[ I≥1 ∩ I=I' ∩ h≢h' ]
  ≥⟨ Pr[A∩B∩~C] I≥1 I=I' h=h' ⟩
    Pr[ I≥1 ∩ I=I' ] − Pr[ I≥1 ∩ h=h' ]
  ≡⟨ −= refl lemma1-5 ⟩
    Pr[ I≥1 ∩ I=I' ] − (Pr[ I≥1 ] /#h)
  ≡⟨by-definition⟩
    Pr[ I≥1 ∩ I=I' ] − (Pr[ acc ] /#h)
  ≥⟨ −-mono lemma1-4 ⟩
    Pr[ acc ] ² /q − (Pr[ acc ] /#h)
  ≡⟨ −= *-assoc refl ⟩
  Pr[ acc ] * Pr[ acc ] /q − Pr[ acc ] * 1/#h
  ≡⟨ ! *-−-distr ⟩
    Pr[ acc ] * ((Pr[ acc ] /q) − 1/#h)
  ∎

-- -}
-- -}
-- -}
-- -}
-- -}
