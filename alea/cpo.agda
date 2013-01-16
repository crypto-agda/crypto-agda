module alea.cpo where

import Data.Nat.NP as Nat

import Relation.Binary.PropositionalEquality as ≡

record Order (A : Set) : Set₁ where
  constructor mk
  infix 4 _≡_ _≤_
  field
    _≤_ : A → A → Set
    _≡_ : A → A → Set
    reflexive : ∀ {x} → x ≤ x
    antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
    transitive : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

  ≡-reflexive : ∀ {x} → x ≡ x
  ≡-reflexive = antisym reflexive reflexive
    
ℕ : Order Nat.ℕ
ℕ = mk Nat._≤_ ≡._≡_ Nat.ℕ≤.refl Nat.ℕ≤.antisym Nat.ℕ≤.trans

funOrder : ∀ {A B : Set} → Order B → Order (A → B)
funOrder or = mk (λ f g  → ∀ x → f x ≤ g x) (λ f g → ∀ x → f x ≡ g x)
              (λ x₁ → reflexive)
              (λ f g x → antisym (f x) (g x)) 
              (λ f g x  → transitive (f x) (g x))
  where open Order or

_o→_ : ∀ A {B} → Order B → Order (A → B)
A o→ ob = funOrder {A} ob
  
record _→m_ {A B}(oa : Order A)(ob : Order B) : Set where
  constructor mk
  field
    _$_ : A → B
    mon : ∀ {x y} → Order._≤_ oa x y → Order._≤_ ob (_$_ x) (_$_ y)
open _→m_ using (_$_ ; mon)

_o→m_ : ∀ {A B}(oa : Order A)(ob : Order B) → Order (oa →m ob)
_o→m_ {A} oa ob = mk (λ f g → _$_ f ≤ _$_ g)
                     (λ f g → _$_ f ≡ _$_ g)
                     reflexive antisym transitive
  where open Order (A o→ ob)

_∘m_ : ∀ {A B C}{oa : Order A}{ob : Order B}{oc : Order C}
     → (ob →m oc) → (oa →m ob) → (oa →m oc)
f ∘m g = mk (λ x → f $ (g $ x)) (λ x → mon f (mon g x))

_$m_ : ∀ {A B C}{oa : Order A}{oc : Order C} → oa →m (funOrder {B} oc)
     → B → oa →m oc
_$m_ {oa = oa}{oc} f b = mk (λ a → (f $ a) b) (λ x≤y → mon f x≤y b )

UB : ∀ {A} → Order A → A → Set
UB or a = ∀ x → x ≤ a
  where open Order or

record cpo {D} (o : Order D) : Set where
  constructor mk
  open Order o

  field
    d0 : D
    lub : (f : ℕ →m o) → D

  -- proofs
  field
    Dbot : ∀ x → d0 ≤ x
    lubUB : ∀ (f : ℕ →m o) n → (f $ n) ≤ lub f
    lubLUB : ∀ (f : ℕ →m o) x → (∀ n → (f $ n) ≤ x) → lub f ≤ x

funcpo : ∀ {A D}{od : Order D} → cpo od → cpo (A o→ od)
funcpo cpod = mk (λ x → d0) (λ f x → lub (f $m x)) (λ x x₁ → Dbot (x x₁)) (λ f n x → lubUB (f $m x) n)
  (λ f x x₁ x₂ → lubLUB (f $m x₂) (x x₂) (λ n → x₁ n x₂))
  where
    open cpo cpod
    open Nat
    open ≡ using (_≡_)

_c→m_ : ∀ {A D}(oa : Order A){od : Order D} → cpo od → cpo (oa o→m od)
_c→m_ {A} oa {od} cpod = mk (mk (λ x → d0) (λ x₁ → Order.reflexive od))
                        (λ f → mk (cpo.lub (funcpo {A} cpod)
                                     (mk (λ n a → (f $ n) $ a) (mon f)))
                                  (λ x≤y → lubLUB _ _ (λ n → transitive (mon (f $ n) x≤y) (lubUB _ n)))) 
                        (λ x x₁ → Dbot (x $ x₁))
                        (λ f n x → lubUB (mk (λ m → (f $ m) $ x) (λ x₂ → mon f x₂ x)) n)
                        (λ f x x₁ x₂ → lubLUB (mk (λ n → _$_ (f $ n)) (mon f) $m x₂) (x $ x₂) (λ n → x₁ n x₂))
  where
    open cpo cpod
    open Order od renaming (_≤_ to _≤ᵈ_)
    open Order oa using () renaming (_≤_ to _≤ᵃ_)

record continous {A B}{oa : Order A}{ob : Order B}
                 (c1 : cpo oa)(c2 : cpo ob)(f : oa →m ob) : Set where
  constructor mk
  open cpo c1 renaming (lub to luba ; lubUB to lubUBa ; lubLUB to lubLUBa)
  open cpo c2
  open Order ob
  field
    contIntro : ∀ (h : ℕ →m oa) → (f $ (luba h)) ≤ lub (f ∘m h)

  contIntro' : ∀ (h : ℕ →m oa) → lub (f ∘m h) ≤ f $ luba h
  contIntro' h = lubLUB (f ∘m h) (f $ luba h) (λ n → mon f (lubUBa _ n))

  contEq : ∀ (h : ℕ →m oa) → (f $ (luba h)) ≡ lub (f ∘m h)
  contEq h = antisym (contIntro h) (contIntro' h)
  
open continous

postulate
  Ur  : Set -- the set [0,1]
  oUr : Order Ur
  U   : cpo oUr

record distr A : Set where
  constructor mk
  field
    μ : (A o→ oUr) →m oUr
    muContinous : continous (funcpo U) U μ

open distr

distrOrder : ∀ A → Order (distr A)
distrOrder A = mk (λ f g → μ f ≤ μ g) (λ f g → μ f ≡ μ g)
  (λ {x} → reflexive {μ x}) (λ {x} {y} → antisym {μ x} {μ y}) (λ {x} {y} {z} → transitive {μ x} {μ y} {μ z}) 
  where
    open Order ((A o→ oUr) o→m oUr)

distrcpo : ∀ A → cpo (distrOrder A)
distrcpo A = mk (mk d0 (mk (λ h → lubUB (mk (λ z → mk (_) (_)) (_)) {!!} {!!})))
                (λ f → mk (lub (mk (λ x → μ (f $ x)) (mon f))) (mk (λ h → {!!})))
                {!!}
                {!!}
                {!!}
  where
     open cpo ((A o→ oUr) c→m U)
    
module FIXPOINTS {d} {D : Order d} {c : cpo D} where
  open cpo c
  open Order D

  iter : (f : D →m D) → Nat.ℕ → d
  iter f Nat.zero = d0
  iter f (Nat.suc n) = f $ iter f n

  iter-mon : (f : D →m D) → ℕ →m D
  iter-mon f = mk (iter f) mono
    where
      mono : ∀ {x y} → x Nat.≤ y → iter f x ≤ iter f y
      mono Nat.z≤n = Dbot _
      mono (Nat.s≤s prf) = mon f (mono prf)

  fix : (f : D →m D) → d
  fix f = lub (iter-mon f)

  fix-le : (F : D →m D) → fix F ≤ F $ (fix F)
  fix-le F = lubLUB _ _ prf
    where
      prf : (n : Nat.ℕ) → iter-mon F $ n ≤ F $ fix F
      prf Nat.zero = Dbot (F $ fix F)
      prf (Nat.suc n) = mon F (lubUB (iter-mon F) n)
  
module _ where

  open Order oUr
  open cpo U

  Munit : ∀ {A} → A → distr A
  Munit x = mk (mk (λ f → f x) (λ x≤y → x≤y x)) (mk (λ h → reflexive))

  Mlet : ∀ {A B} → distr A → (A → distr B) → distr B
  Mlet m k = mk (mk (λ f → μ m $ (λ x → μ (k x) $ f)) (λ x≤y → mon (μ m) (λ x → mon (μ (k x)) x≤y)))
     (mk (λ h → transitive (mon (μ m) (λ x → contIntro (muContinous (k x)) h)) (contIntro (muContinous m) _)))

  Munit-simpl : ∀ {A}(q : A → Ur) x → μ (Munit x) $ q ≡ q x
  Munit-simpl q x = ≡-reflexive

  Mlet-simpl : ∀ {A B}(m : distr A)(M : A → distr B)(f : B → Ur)
             → μ (Mlet m M) $ f ≡ μ m $ (λ x → μ (M x) $ f) 
  Mlet-simpl m M f = ≡-reflexive

  Mlet-le-compat : ∀ {A B} (m1 m2 : distr A)(M1 M2 : A → distr B)
    → Order._≤_ (distrOrder A) m1 m2
    → Order._≤_ (A o→ distrOrder B) M1 M2
    → Order._≤_ (distrOrder B) (Mlet m1 M1) (Mlet m2 M2)
  Mlet-le-compat m1 m2 M1 M2 m1≤m2 M1≤M2 f = transitive (mon (μ m1) (λ x → M1≤M2 x f)) (m1≤m2 _)

  -- Monad laws

  Mlet-unit : ∀ {A B} (x : A)(m : A → distr B)
            → Order._≡_ (distrOrder B) (Mlet (Munit x) m) (m x)
  Mlet-unit x m f = ≡-reflexive

  Mlet-ext : ∀ {A}(m : distr A) → Order._≡_ (distrOrder A) (Mlet m Munit) m
  Mlet-ext m f = ≡-reflexive

  Mlet-assoc : ∀ {A B C}(m1 : distr A)(m2 : A → distr B)(m3 : B → distr C)
             → Order._≡_ (distrOrder C)
                (Mlet (Mlet m1 m2) m3)
                (Mlet m1 (λ x → Mlet (m2 x) m3))
  Mlet-assoc m1 m2 m3 f = ≡-reflexive
