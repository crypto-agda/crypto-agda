{-# OPTIONS --without-K #-}
{-# OPTIONS --copatterns #-}
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
  coinductive
  constructor mk
  field
    _$_ : A → B
    .mon : ∀ {x y} → Order._≤_ oa x y → Order._≤_ ob (_$_ x) (_$_ y)
open _→m_ using (_$_ ; mon)

_o→m_ : ∀ {A B}(oa : Order A)(ob : Order B) → Order (oa →m ob)
_o→m_ {A} oa ob = mk (λ f g → _$_ f ≤ _$_ g)
                     (λ f g → _$_ f ≡ _$_ g)
                     reflexive antisym transitive
  where open Order (A o→ ob)

swapm : ∀ {A B C}{oa : Order A}{ob : Order B}{oc : Order C}
      → oa →m (ob o→m oc) → ob →m (oa o→m oc)
swapm f = mk (λ b → mk (λ a → (f $ a) $ b) (λ r → mon f r b )) (λ r x → mon (f $ x) r)

swapm' : ∀ {A B C}{oa : Order A}{ob : Order B}{oc : Order C}
      → oa →m (ob o→m oc) → ob →m (oa o→m oc)
_$_ (_$_ (swapm' f) b) a = (f $ a) $ b
mon (_$_ (swapm' f) b) r = mon f r b
mon (swapm' f) r x = mon (f $ x) r

{-
swapm'' : ∀ {A B C}{oa : Order A}{ob : Order B}{oc : Order C}
      → oa →m (ob o→m oc) → ob →m (oa o→m oc)
(swapm'' f $ b)    $ a = (f $ a) $ b
mon (swapm' f $ b) r   = mon f r b
mon (swapm' f)     r x = mon (f $ x) r
-}

_∘m_ : ∀ {A B C}{oa : Order A}{ob : Order B}{oc : Order C}
     → (ob →m oc) → (oa →m ob) → (oa →m oc)
f ∘m g = mk (λ x → f $ (g $ x)) (λ x → mon f (mon g x))

_∘m'_ : ∀ {A B C}{oa : Order A}{ob : Order B}{oc : Order C}
     → (ob →m oc) → (oa →m ob) → (oa →m oc)
_$_ (f ∘m' g) x = f $ (g $ x)
mon (f ∘m' g) x = mon f (mon g x)

_$m_ : ∀ {A B C}{oa : Order A}{oc : Order C}
       → oa →m (B o→ oc) → B → oa →m oc
_$m_ {oa = oa}{oc} f b = mk (λ a → (f $ a) b) (λ x≤y → mon f x≤y b )

_$m'_ : ∀ {A B C}{oa : Order A}{oc : Order C} → oa →m (funOrder {B} oc)
     → B → oa →m oc
_$_ (f $m' b) a   = (f $ a) b
mon (f $m' b) x≤y = mon f x≤y b

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
    .Dbot : ∀ x → d0 ≤ x
    .lubUB : ∀ (f : ℕ →m o) n → (f $ n) ≤ lub f
    .lubLUB : ∀ (f : ℕ →m o) x → (∀ n → (f $ n) ≤ x) → lub f ≤ x

  .lub-ext : ∀ {f g} → Order._≤_ (ℕ o→m o) f g → lub f ≤ lub g
  lub-ext {f} {g} f≤g = lubLUB f (lub g) (λ n → transitive (f≤g n) (lubUB g n))

  lubm : (ℕ o→m o) →m o
  lubm = mk lub (λ {a}{b} x₁ → lub-ext {mk (λ z → a $ z) (mon a)}{mk (λ z → b $ z) (mon b)} x₁)

  lubm' : (ℕ o→m o) →m o
  _$_ lubm' = lub
  mon lubm' {a}{b} x₁ = lub-ext {mk (λ z → a $ z) (mon a)}{mk (λ z → b $ z) (mon b)} x₁

module _ where
  .lub-swap : ∀ {D}{o : Order D}(c : cpo o)
             → let open cpo c
                   open Order o
               in ∀ f → lub (lubm ∘m f) ≤ lub (lubm ∘m swapm f)
  lub-swap {D}{o} c f = lubLUB (lubm ∘m f) (lub (lubm ∘m swapm f))
                     (λ n → lubLUB (f $ n) (lub (lubm ∘m swapm f))
                     (λ n₁ → transitive (lubUB (swapm f $ n₁) n) (lubUB (lubm ∘m swapm f) n₁)))
    where
      open cpo c
      open Order o

  funcpo : ∀ {A D}{od : Order D} → cpo od → cpo (A o→ od)
  funcpo {A}{D}{od}cpod = mk fbot flub fDbot flubUB flubLUB
    where
      module D = cpo cpod
      open Nat
      open ≡ using (_≡_)
      fbot : A → D
      fbot _ = D.d0
      flub : _ → _
      flub f = λ x → D.lub (f $m x)
      .fDbot : (_ : _) → _
      fDbot f = λ x → D.Dbot (f x)
      .flubUB : (_ : _) → _
      flubUB f = λ n x → D.lubUB (f $m x) n
      .flubLUB : (_ : _) → _
      flubLUB f = λ x x₁ x₂ → D.lubLUB (f $m x₂) (x x₂) (λ n → x₁ n x₂)

  _c→m_ : ∀ {A D}(oa : Order A){od : Order D} → cpo od → cpo (oa o→m od)
  _c→m_ {A} oa {od} cpod = mk (mk (λ x → d0) (λ x₁ → Order.reflexive od))
                          (λ f → mk (cpo.lub (funcpo {A} cpod)
                                       (mk (λ n a → (f $ n) $ a) (mon f)))
                                    (λ {x}{y}x≤y → lubLUB _ _ (λ n → transitive (mon (f $ n) x≤y) (lubUB (mk (λ v → (f $ v) $ y) (λ r → mon f r y)) n))))
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
    .contIntro : ∀ (h : ℕ →m oa) → (f $ (luba h)) ≤ lub (f ∘m h)

  .contIntro' : ∀ (h : ℕ →m oa) → lub (f ∘m h) ≤ f $ luba h
  contIntro' h = lubLUB (f ∘m h) (f $ luba h) (λ n → mon f (lubUBa _ n))

  .contEq : ∀ (h : ℕ →m oa) → (f $ (luba h)) ≡ lub (f ∘m h)
  contEq h = antisym (contIntro h) (contIntro' h)
  
open continous

module Distr
  (Ur  : Set) -- the set [0,1]
  (1/_+1 : Nat.ℕ → Ur)
  (_+_ : Ur → Ur → Ur)
  (_×_ : Ur → Ur → Ur)
  (oUr : Order Ur)
  (≤-cong-+ : let open Order oUr in ∀ {x y z w} → x ≤ z → y ≤ w → x + y ≤ z + w)
  (≤-cong-× : let open Order oUr in ∀ {x y z w} → x ≤ z → y ≤ w → x × y ≤ z × w)
  (U   : cpo oUr) where

  record distr A : Set where
    constructor mk
    field
      μ : (A o→ oUr) →m oUr
      .muContinous : ∀ (h : ℕ →m (A o→ oUr)) → Order._≤_ oUr (μ $ cpo.lub (funcpo U) h) (cpo.lub U (μ ∘m h)) -- continous (funcpo U) U μ

  open distr

  module _ A where
    module M = cpo ((A o→ oUr) c→m U)

    distrOrder : Order (distr A)
    distrOrder = mk (λ f g → μ f ≤ μ g) (λ f g → μ f ≡ μ g)
      (λ {x} → reflexive {μ x}) (λ {x} {y} → antisym {μ x} {μ y}) (λ {x} {y} {z} → transitive {μ x} {μ y} {μ z})
      where open Order ((A o→ oUr) o→m oUr)

    μm : distrOrder →m ((A o→ oUr) o→m oUr)
    μm = mk μ (λ x₁ x₂ → x₁ x₂)

    distrcpo : cpo distrOrder
    distrcpo = mk (mk M.d0 (λ h → cpo.Dbot U (cpo.lub U (M.d0 ∘m h))))

                    (λ f → mk (M.lub (μm ∘m f)) (λ h → transitive
                                                       (cpo.lub-ext U (λ a → muContinous (f $ a) h))
                                                       (lub-swap U (mk (λ z → mk (λ z₁ → μ (f $ z) $ (h $ z₁))
                                                                                 (λ x → mon (μ (f $ z)) (mon h x)))
                                                                       (λ {x}{y} x₁ x₂ →
                                                                              mon f x₁ (λ x₃ → (h $ x₂) x₃))))))
                    (λ x x₁ → cpo.Dbot U (μ x $ x₁))
                    (λ f n x → cpo.lubUB U _ _ )
                    (λ f x x₁ x₂ → cpo.lubLUB U _ _ (λ n → x₁ n x₂))
       where open Order oUr

  module FIXPOINTS {d} {D : Order d} {c : cpo D} where
    open cpo c
    open Order D

    iter : (f : D →m D) → Nat.ℕ → d
    iter f Nat.zero = d0
    iter f (Nat.suc n) = f $ iter f n

    iter-mon : (f : D →m D) → ℕ →m D
    iter-mon f = mk (iter f) mono
      where
        .mono : ∀ {x y} → x Nat.≤ y → iter f x ≤ iter f y
        mono Nat.z≤n = Dbot _
        mono (Nat.s≤s prf) = mon f (mono prf)

    fix : (f : D →m D) → d
    fix f = lub (iter-mon f)

    .fix-le : (F : D →m D) → fix F ≤ F $ (fix F)
    fix-le F = lubLUB _ _ prf
      where
        .prf : (n : Nat.ℕ) → iter-mon F $ n ≤ F $ fix F
        prf Nat.zero = Dbot (F $ fix F)
        prf (Nat.suc n) = mon F (lubUB (iter-mon F) n)



  module _ where

    open Order oUr
    open cpo U
    open import Data.Bool

    postulate
      EXPLODE : ∀ {A : Set} → A


    flip : distr Bool
    _$_ (μ flip) f = (1/ 1 +1 × f true) + (1/ 1 +1 × f false)
    mon (μ flip) r = ≤-cong-+ (≤-cong-× reflexive (r true)) (≤-cong-× reflexive (r false))
    muContinous flip h = EXPLODE

    Munit : ∀ {A} → A → distr A
    Munit x = mk (mk (λ f → f x) (λ x≤y → x≤y x)) (λ h → reflexive)

    Mlet : ∀ {A B} → distr A → (A → distr B) → distr B
    Mlet m k = mk (mk (λ f → μ m $ (λ x → μ (k x) $ f)) (λ x≤y → mon (μ m) (λ x → mon (μ (k x)) x≤y)))
       (λ h →  transitive (mon (μ m) (λ x → muContinous (k x) h))
                   (muContinous m (mk (λ z z₁ → μ (k z₁) $ (h $ z)) (λ x₁ x₂ → mon (μ (k x₂)) (mon h x₁)))))

    Munit-simpl : ∀ {A}(q : A → Ur) x → μ (Munit x) $ q ≡ q x
    Munit-simpl q x = ≡-reflexive

    Mlet-simpl : ∀ {A B}(m : distr A)(M : A → distr B)(f : B → Ur)
               → μ (Mlet m M) $ f ≡ μ m $ (λ x → μ (M x) $ f)
    Mlet-simpl m M f = ≡-reflexive

    .Mlet-le-compat : ∀ {A B} (m1 m2 : distr A)(M1 M2 : A → distr B)
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

