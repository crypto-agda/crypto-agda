module Prob where

open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Sum

open import Function

open import Relation.Binary.PropositionalEquality.NP
open import Relation.Nullary

record ]0,1[-ops (]0,1[ : Set) (_<E_ : ]0,1[ → ]0,1[ → Set) : Set where
  constructor mk

  field
    -- 1E : ]0,1]
    1+_/1+x_ : ℕ → ℕ → ]0,1[
    _+E_ : ]0,1[ → ]0,1[ → ]0,1[
    _·E_ : ]0,1[ → ]0,1[ → ]0,1[
    _/E_<_> : (x y : ]0,1[) → x <E y → ]0,1[
    1-E_ : ]0,1[ → ]0,1[

   -- proofs <E
  field
    <E-trans : ∀ {x y z} → x <E y → y <E z → x <E z

  field
    +E-mono₁ : ∀ x {y} → y <E (y +E x)
    +E-mono₂ : ∀ x {y z} → y <E z → (x +E y) <E (x +E z)
    ·E-anti₁ : (x : ]0,1[){y : ]0,1[} → (x ·E y) <E y
    ·E-anti₂ : (x : ]0,1[){y z : ]0,1[} → y <E z → (x ·E y) <E z
    ·/E-assoc : (x y z : ]0,1[)(pf : y <E z) → x ·E (y /E z < pf >) ≡ (x ·E y) /E z < ·E-anti₂ x pf >

  -- proofs ≡ maybe should be some Equivalence ≈
  field
    +E-sym : (x y : ]0,1[) → x +E y ≡ y +E x
    +E-assoc : (x y z : ]0,1[) → (x +E y) +E z ≡ x +E (y +E z)
    ·/E-identity : (x : ]0,1[){y : ]0,1[} → x ≡ (x ·E y) /E y < ·E-anti₁ x >

module ]0,1[-ℚ where
  data ]0,1[ : Set where
    1+_/2+x+_ : ℕ → ℕ → ]0,1[
  -- toℚ : ]0,1] → ℚ
  -- toℚ (1+ x /1+x+ y) = (1 + x) /ℚ (1 + x + y)

  postulate
    _<E_ : ]0,1[ → ]0,1[ → Set
  -- (1+ x /1+x+ y) ≤E (1+ x' /1+x+ y') = ?
  -- (1 + x' + y') * (1 + x) ≤E (1 + x + y) * (1 + x') = ?

  -- 1 - ((1 + x) / (2 + x + y))
  --  ≡ (2 + x + y - (1 + x)) / (2 + x + y)
  --  ≡ (1 + y) / (2 + x + y)
  --  ≡ (1 + y) / (2 + y + x)
  1-E_ : ]0,1[ → ]0,1[
  1-E (1+ x /2+x+ y) = 1+ y /2+x+ x

  -- ((1 + x) / (2 + x + y)) · ((1 + x') / (2 + x' + y'))
  --  ≡ ((1 + x) · (1 + x')) / ((2 + x + y) · (2 + x' + y'))
  --  ≡ (1 + x + x' + x · x') / (4 + 2x + 2y + 2x' + 2y' + xx' + xy' + yx' + yy')
  --  ≡ (1 + (x + x' + xx')) / (2 + (x + x' + xx') + (2 + x + 2y + x' + xy' + yx' + yy'))
  _·E_ : ]0,1[ → ]0,1[ → ]0,1[
  (1+ x /2+x+ y) ·E (1+ x' /2+x+ y') = 1+ x'' /2+x+ y''
    where x'' = x + x' + x * x'
          y'' = 2 + x + 2 * y + x' + x * y' + y * x' + y * y'

  -- ((1 + x) / (2 + x + y)) / ((1 + x') / (2 + x' + y'))
  --   ≡ ((1 + x) · (2 + x' + y')) / ((1 + x') · (2 + x + y))
  --   ≡ (2 + x' + y' + 2x + xx' + xy') / (2 + x + y + 2x' + xx' + x'y)
  --   ≡ (1 + (1 + x' + y' + 2x + xx' + xy')) / (2 + (1 + x' + y' + 2x + xx' + xy') + y + x' + x'y - (1 + y' + x + xy'))
  --   ok provided that:
  --   ((1 + x) / (2 + x + y)) < ((1 + x') / (2 + x' + y'))
  --   implies
  --   (1 + y' + x + xy') ≤ (y + x' + x'y)
  --   which remains to be checked
  _/E_<_> : (x y : ]0,1[) → x <E y → ]0,1[
  (1+ x /2+x+ y) /E (1+ x' /2+x+ y') < _ > = 1+ x'' /2+x+ y''
    where x'' = 1 + x' + y' + 2 * x + x * x' + x * y'
          y'' = y + x' + x' * y ∸ 1 ∸ y' ∸ x ∸ x * y'

  postulate
    _+E_ : ]0,1[ → ]0,1[ → ]0,1[

  postulate
    <E-trans : ∀ {x y z} → x <E y → y <E z → x <E z

  postulate
    +E-mono₁ : ∀ x {y} → y <E (y +E x)
    +E-mono₂ : ∀ x {y z} → y <E z → (x +E y) <E (x +E z)
    ·E-anti₁ : (x : ]0,1[) {x₁ : ]0,1[} → (x ·E x₁) <E x₁
    ·E-anti₂ : (x : ]0,1[){y z : ]0,1[} → y <E z → (x ·E y) <E z
    ·/E-assoc : (x y z : ]0,1[)(pf : y <E z) → x ·E (y /E z < pf >) ≡ (x ·E y) /E z < ·E-anti₂ x pf >

  postulate
    +E-sym : (x x₁ : ]0,1[) → x +E x₁ ≡ x₁ +E x
    +E-assoc : (x x₁ x₂ : ]0,1[) → (x +E x₁) +E x₂ ≡ x +E (x₁ +E x₂)
    ·/E-identity : (x : ]0,1[) {y : ]0,1[} → x ≡ (x ·E y) /E y < ·E-anti₁ x >

  ops : ]0,1[-ops ]0,1[ _<E_
  ops = mk 1+_/2+x+_ _+E_ _·E_ _/E_<_> 1-E_ <E-trans +E-mono₁ +E-mono₂ ·E-anti₁ ·E-anti₂ ·/E-assoc +E-sym +E-assoc ·/E-identity

module [0,1] {]0,1[ _<E_} (]0,1[R : ]0,1[-ops ]0,1[ _<E_) where

  open ]0,1[-ops ]0,1[R public

  infixl 6 _+I_
  infix 4 _≤I_

  data [0,1] : Set where
   0I : [0,1]
   1I : [0,1]
   _I : ]0,1[ → [0,1]

  data _≤I_ : [0,1] → [0,1] → Set where
    z≤n : ∀ {n} → 0I ≤I n
    n≤1 : ∀ {n} → n ≤I 1I
    E≤E : ∀ {x y} → x <E y → (x I) ≤I (y I)
    E≡E : ∀ {x} → x I ≤I x I


  ≤I-refl : ∀ {x} → x ≤I x
  ≤I-refl {0I} = z≤n
  ≤I-refl {1I} = n≤1
  ≤I-refl {x I} = E≡E

  Pos : [0,1] → Set
  Pos 0I    = ⊥
  Pos 1I    = ⊤
  Pos (_ I) = ⊤

  Inc : [0,1] → Set
  Inc 0I = ⊥
  Inc 1I = ⊥
  Inc (x I) = ⊤

  _<_> : (x : [0,1]) → Inc x → ]0,1[
  0I < () >
  1I < () >
  (x I) < pos > = x

  _+I_ : [0,1] → [0,1] → [0,1]
  0I +I x = x
  1I +I _ = 1I
  x I +I 0I = x I
  x I +I 1I = 1I
  x I +I x₁ I = (x +E x₁) I

  _·I_ : [0,1] → [0,1] → [0,1]
  0I ·I y = 0I
  1I ·I y = y
  (x I) ·I 0I     = 0I
  (x I) ·I 1I     = x I
  (x I) ·I (x₁ I) = (x ·E x₁) I

  -- 1/I1+_ : ℕ → [0,1]


  _/I_<_,_> : (x y : [0,1]) → x ≤I y → Pos y → [0,1]
  x /I 0I    < _        , () >
  x /I 1I    < _        , _  > = x
  0I /I _    < _        , _  > = 0I
  1I /I _ I  < ()       , _  >
  (x I) /I y I < E≤E pf , _  > = (x /E y < pf >) I
  (x I) /I .x I < E≡E   , _  > = 1I


  +I-identity : (x : [0,1]) → x ≡ 0I +I x
  +I-identity x = refl

  *-anti : (x : [0,1]){y z : [0,1]} → y ≤I z → x ·I y ≤I z
  *-anti 0I le = z≤n
  *-anti 1I le = le
  *-anti (x I) z≤n = z≤n
  *-anti (x I) n≤1 = n≤1
  *-anti (x I) (E≤E pf) = E≤E (·E-anti₂ x pf)
  *-anti (x I) E≡E = E≤E (·E-anti₁ x)

  */-assoc : (x y z : [0,1])(pr : y ≤I z)(pos : Pos z) → (x ·I (y /I z < pr , pos >)) ≡ (x ·I y) /I z < *-anti x pr , pos >
  */-assoc x y 0I pr ()
  */-assoc x y 1I pr pos = refl
  */-assoc 0I y (z I) pr pos = refl
  */-assoc 1I y (z I) pr pos = refl
  */-assoc (x I) 0I (z I) pr pos = refl
  */-assoc (x I) 1I (z I) () pos
  */-assoc (x I) (y I) (z I) (E≤E pf) pos = cong _I (·/E-assoc x y z pf)
  */-assoc (x I) (y I) (.y I) E≡E pos = cong _I (·/E-identity x)

  +I-sym : (x y : [0,1]) → x +I y ≡ y +I x
  +I-sym 0I 0I = refl
  +I-sym 0I 1I = refl
  +I-sym 0I (x I) = refl
  +I-sym 1I 0I = refl
  +I-sym 1I 1I = refl
  +I-sym 1I (x I) = refl
  +I-sym (x I) 0I = refl
  +I-sym (x I) 1I = refl
  +I-sym (x I) (y I) = cong _I (+E-sym x y)

  +I-assoc : (x y z : [0,1]) → x +I y +I z ≡ x +I (y +I z)
  +I-assoc 0I y z = refl
  +I-assoc 1I y z = refl
  +I-assoc (x I) 0I z = refl
  +I-assoc (x I) 1I z = refl
  +I-assoc (x I) (y I) 0I = refl
  +I-assoc (x I) (y I) 1I = refl
  +I-assoc (x I) (y I) (z I) = cong _I (+E-assoc x y z)

  ≤I-trans : {x y z : [0,1]} → x ≤I y → y ≤I z → x ≤I z
  ≤I-trans z≤n le2 = z≤n
  ≤I-trans n≤1 n≤1 = n≤1
  ≤I-trans (E≤E x₁) n≤1 = n≤1
  ≤I-trans (E≤E x₁) (E≤E x₂) = E≤E (<E-trans x₁ x₂)
  ≤I-trans (E≤E x₁) E≡E = E≤E x₁
  ≤I-trans E≡E le2 = le2

  ≤I-mono  : (x : [0,1]){y z : [0,1]} → y ≤I z → y ≤I z +I x
  ≤I-mono 0I {z = z} le rewrite +I-sym z 0I = le
  ≤I-mono 1I {z = z} le rewrite +I-sym z 1I = n≤1
  ≤I-mono (x I) z≤n = z≤n
  ≤I-mono (x I) n≤1 = n≤1
  ≤I-mono (x I) (E≤E x₂) = E≤E (<E-trans x₂ (+E-mono₁ x))
  ≤I-mono (x I) E≡E = E≤E (+E-mono₁ x)

  ≤I-pres  : (x : [0,1]){y z : [0,1]} → y ≤I z → x +I y ≤I x +I z
  ≤I-pres 0I le = le
  ≤I-pres 1I le = n≤1
  ≤I-pres (x I) {.0I} {0I} z≤n = E≡E
  ≤I-pres (x I) {.0I} {1I} z≤n = n≤1
  ≤I-pres (x I) {.0I} {x₁ I} z≤n = E≤E (+E-mono₁ x₁)
  ≤I-pres (x I) n≤1 = n≤1
  ≤I-pres (x I) (E≤E x₂) = E≤E (+E-mono₂ x x₂)
  ≤I-pres (x I) E≡E = E≡E


module Univ {]0,1[ _<E_} (]0,1[R : ]0,1[-ops ]0,1[ _<E_)
            (U : Set)
            (size-1 : ℕ)
            (allU : Vec U (suc size-1))
            (x∈allU : (x : U) → x ∈ allU)  where

  open [0,1] ]0,1[R

  sumP : {n : ℕ} → (U → [0,1]) → Vec U n → [0,1]
  sumP pmf []       = 0I
  sumP pmf (x ∷ xs) = (pmf x) +I (sumP pmf xs)

  record Distr : Set where
    constructor _,_
    field
      -- Probability mass function: http://en.wikipedia.org/wiki/Probability_mass_function
      pmf    : U → [0,1]
      sum≡1 : sumP pmf allU ≡ 1I

  module Prob (d : Distr) where
    open Distr d

    Event : Set
    Event = U → Bool

    pr_∋_ : Event → U → [0,1]
    pr A ∋ x = if A x then pmf x else 0I

    _∪_ : Event → Event → Event
    A₁ ∪ A₂ = λ x → A₁ x ∨ A₂ x

    _∩_ : Event → Event → Event
    A₁ ∩ A₂ = λ x → A₁ x ∧ A₂ x

    _⊆_ : Event → Event → Set
    A ⊆ B = ∀ x → T(A x) → T(B x)

    ℂ[_] : Event → Event
    ℂ[ A ] = not ∘ A

    Pr[_] : Event → [0,1]
    Pr[ A ] = sumP (pr_∋_ A) allU

    postulate
      Pr-mono : ∀ {A B} → A ⊆ B → Pr[ A ] ≤I Pr[ B ]

    ∪-lem : ∀ {A} B → A ⊆ (A ∪ B)
    ∪-lem {A} _ x with A x
    ... | true = id
    ... | false = λ()

    ∩-lem : ∀ A {B} → (A ∩ B) ⊆ B
    ∩-lem A x with A x
    ... | true  = id
    ... | false = λ()

    Pr[_∣_]<_> : (A B : Event)(pf : Pos Pr[ B ]) → [0,1]
    Pr[ A ∣ B ]< pr > = Pr[ A ∩ B ] /I Pr[ B ] < Pr-mono (∩-lem A) , pr >

    _ind_ : (A B : Event) → Set
    A ind B = Pr[ A ] ·I Pr[ B ] ≡ Pr[ A ∩ B ]

    union-bound : (A₁ A₂ : Event) → Pr[ (A₁ ∪ A₂) ] ≤I Pr[ A₁ ] +I Pr[ A₂ ]
    union-bound A₁ A₂ = go allU where
      sA₁ : {n : ℕ} → Vec U n → [0,1]
      sA₁ = λ xs → sumP (pr_∋_ A₁) xs
      sA₂ : {n : ℕ} → Vec U n → [0,1]
      sA₂ = sumP (pr_∋_ A₂)
      go : {n : ℕ}(xs : Vec U n) → sumP (pr_∋_ (A₁ ∪ A₂)) xs ≤I sumP (pr_∋_ A₁) xs +I sumP (pr_∋_ A₂) xs
      go [] = ≤I-refl
      go (x ∷ xs) with A₁ x | A₂ x
      ... | true  | true  rewrite +I-assoc (pmf x) (sA₁ xs) (pmf x +I sA₂ xs)
                                | +I-sym (pmf x) (sA₂ xs)
                                | sym (+I-assoc (sA₁ xs) (sA₂ xs) (pmf x))
                                = ≤I-pres (pmf x) (≤I-mono (pmf x) (go xs))
      ... | true  | false rewrite +I-assoc (pmf x) (sA₁ xs) (sA₂ xs)
                                = ≤I-pres (pmf x) (go xs)
      ... | false | true  rewrite sym (+I-assoc (sA₁ xs) (pmf x) (sA₂ xs))
                                | +I-sym (sA₁ xs) (pmf x)
                                | +I-assoc (pmf x) (sA₁ xs) (sA₂ xs)
                                = ≤I-pres (pmf x) (go xs)
      ... | false | false = go xs

    module RandomVar (V : Set) (_==V_ : V → V → Bool) where
       RV : Set
       RV = U → V

       _^-1_ : RV → V → Event
       RV ^-1 v = λ x → RV x ==V v

       _≡r_ : RV → V → Event
       RV ≡r v = RV ^-1 v

       -- sugar, socker et sucre
       Pr[_≡_] : RV → V → [0,1]
       Pr[ X ≡ v ] = Pr[ X ≡r v ]

       -- ∀ (a b) . Pr[X = a and Y = b] = Pr[X = a] · Pr[Y = b]
       _indRV_ : RV → RV → Set
       X indRV Y = (a b : V) → (X ^-1 a) ind (Y ^-1 b)
