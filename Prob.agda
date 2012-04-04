module Prob where

open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Function

open import Relation.Binary.PropositionalEquality.NP
open import Relation.Nullary

record ]0,1]-ops (]0,1] : Set) (_≤E_ : ]0,1] → ]0,1] → Set) : Set where
  constructor mk
  field     
    1E : ]0,1]
    _+E_ : ]0,1] → ]0,1] → ]0,1]
    _·E_ : ]0,1] → ]0,1] → ]0,1]
    _/E_<_> : (x y : ]0,1]) → x ≤E y → ]0,1]

module [0,1] {]0,1] _≤E_} (]0,1]R : ]0,1]-ops ]0,1] _≤E_) where

  open ]0,1]-ops ]0,1]R public

  infixl 6 _+I_
  infix 4 _≤I_

  data [0,1] : Set where
   0I : [0,1]
   _I : ]0,1] → [0,1]

  data _≤I_ : [0,1] → [0,1] → Set where
    z≤n : ∀ {n} → 0I ≤I n
    E≤E : ∀ {x y} → x ≤E y → (x I) ≤I (y I)

  1I : [0,1]
  1I = 1E I

  Pos : [0,1] → Set
  Pos 0I    = ⊥
  Pos (_ I) = ⊤

  _<_> : (x : [0,1]) → Pos x → ]0,1] 
  0I < () >
  (x I) < pos > = x

  _+I_ : [0,1] → [0,1] → [0,1]
  0I +I x = x
  x I +I 0I = x I
  x I +I x₁ I = (x +E x₁) I

  _·I_ : [0,1] → [0,1] → [0,1]
  0I ·I y = 0I
  (x I) ·I 0I = 0I
  (x I) ·I (x₁ I) = (x ·E x₁) I

  -- 1/I1+_ : ℕ → [0,1]

  _/I_<_,_> : (x y : [0,1]) → x ≤I y → Pos y → [0,1]
  _  /I 0I < _ , () >
  0I /I _  < _ , _ > = 0I
  (x I) /I (y I) < E≤E pf , _ > = (x /E y < pf >)I

  +I-identity : (x : [0,1]) → x ≡ 0I +I x
  +I-identity x = refl

  postulate
    +I-sym : (x y : [0,1]) → x +I y ≡ y +I x
    +I-assoc : (x y z : [0,1]) → x +I y +I z ≡ x +I (y +I z)

    ≤I-refl : {x : [0,1]} → x ≤I x

    ≤I-trans : {x y z : [0,1]} → x ≤I y → y ≤I z → x ≤I z
    ≤I-mono  : (x : [0,1]){y z : [0,1]} → y ≤I z → y ≤I z +I x
    ≤I-pres  : (x : [0,1]){y z : [0,1]} → y ≤I z → x +I y ≤I x +I z

module Univ {]0,1] _≤E_} (]0,1]R : ]0,1]-ops ]0,1] _≤E_)
            (U : Set)
            (size-1 : ℕ) 
            (allU : Vec U (suc size-1))
            (x∈allU : (x : U) → x ∈ allU)  where 

  open [0,1] ]0,1]R

  sumP : {n : ℕ} → (U → [0,1]) → Vec U n → [0,1]
  sumP P []       = 0I
  sumP P (x ∷ xs) = (P x) +I (sumP P xs)

  module Prob (P : U → [0,1])
              (sumP≡1 : sumP P allU ≡ 1I) where
    
    Event : Set
    Event = U → Bool 
  
    pr_∋_ : Event → U → [0,1]
    pr A ∋ x = if A x then P x else 0I

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
      ... | true  | true  rewrite +I-assoc (P x) (sA₁ xs) (P x +I sA₂ xs)
                                | +I-sym (P x) (sA₂ xs)
                                | sym (+I-assoc (sA₁ xs) (sA₂ xs) (P x))
                                = ≤I-pres (P x) (≤I-mono (P x) (go xs)) 
      ... | true  | false rewrite +I-assoc (P x) (sA₁ xs) (sA₂ xs)
                                = ≤I-pres (P x) (go xs)
      ... | false | true  rewrite sym (+I-assoc (sA₁ xs) (P x) (sA₂ xs))
                                | +I-sym (sA₁ xs) (P x)
                                | +I-assoc (P x) (sA₁ xs) (sA₂ xs)
                                = ≤I-pres (P x) (go xs)
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
