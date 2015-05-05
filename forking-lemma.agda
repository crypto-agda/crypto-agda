{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Function.NP
open import Data.Nat.NP hiding (_==_)
open import Data.Vec.NP hiding (sum)
open import Data.Maybe
open import Data.One using (𝟙)
open import Data.Two.Base hiding (_==_; _²)
open import Data.Fin.NP as Fin hiding (_+_; _-_; _≤_)
open import Data.Product.NP
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP hiding (J)

module forking-lemma where

{-
_≥1 : ∀ {n} → Fin n → 𝟚
zero  ≥1 = 0₂
suc _ ≥1 = 1₂
-}

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
    q≥1   : q ≥ 1

  #h     : ℕ
  #h≥2   : #h ≥ 2

  #ρ : ℕ
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

#Ω = ((#h ^ q) ^2) * #ρ
-- Ω ≃ Fin #Ω

instance
  #Ω≥1 : #Ω ≥ 1
  #Ω≥1 = {!!}

module M (r : Ω) where
  open Ω r

  F' : (I-1 : Fin q)(σ : Res) → Maybe (Res × Res)
  F' I-1 σ =
    case I=I' ∧ h=h'
      0: nothing
      1: just (σ , σ')
    module F' where
      res' = A (replace I-1 hs hs') ρ
      I'   = fst res'
      σ'   = snd res'
      h    = hs  ‼ I-1
      h'   = hs' ‼ I-1
      I    = suc I-1
      I=I' = I == I'
      h=h' = h == h'

  F : Maybe (Res × Res)
  F =
    case I of λ
    { zero      → nothing
    ; (suc I-1) → F' I-1 σ
    }
    module F where
      res  = A hs ρ
      I    = fst res
      σ    = snd res
      -- I≥1  = not (I == zero)

I≥1∧_ : (f : Ω → Fin q → Res → 𝟚) → Event
(I≥1∧ f) r = case I of λ
             { zero → 0₂
             ; (suc I-1) → f r I-1 σ
             }
  where open M.F r

I≥1 I≥1∧I=I' I≥1∧h=h' I≥1∧I=I'∧h≢h' : Event

I≥1 = I≥1∧ λ _ _ _ → 1₂

I≥1∧I=I'      = I≥1∧ λ r I-1 σ → let open M.F' r I-1 σ in I=I'
I≥1∧h=h'      = I≥1∧ λ r I-1 σ → let open M.F' r I-1 σ in h=h'
I≥1∧I=I'∧h≢h' = I≥1∧ λ r I-1 σ → let open M.F' r I-1 σ in I=I' ∧ not h=h'

I=1+_ I=I'=1+_ : (i : Fin q) → Event

I=1+    i = I≥1∧ λ r I-1 σ → let open M.F' r I-1 σ in I == suc i
I=I'=1+ i = I≥1∧ λ r I-1 σ → let open M.F' r I-1 σ in I == suc i ∧ I=I'

-- Acceptance event for A
acc : Event
acc = I≥1

frk : Event
frk = is-just ∘ M.F

instance
    #h≥1 : #h ≥ 1
    #h≥1 = ℕ≤.trans (s≤s z≤n) #h≥2

infix 0 _≥'_
infixr 2 _≥⟨_⟩_ _≡⟨_⟩_ _≡⟨by-definition⟩_
infix 2 _∎

postulate
  -- [0,1] : Type
  ℝ : Type
  -- [0,1]▹ℝ : [0,1] → ℝ
  -- x - y requires x ≥ y
  -- _·_ : [0,1] → [0,1] → [0,1]
  _-_ _·_ : ℝ → ℝ → ℝ
  -- _-_ :
  -- _-_ : [0,1] → [0,1] → ℝ
  -- _≥'_ : [0,1] → [0,1] → Type
  _≥'_ : ℝ → ℝ → Type
  1/_ : (d : ℕ){{_ : d ≥ 1}} → ℝ

  _≥⟨_⟩_ : ∀ x {y} → x ≥' y → ∀ {z} → y ≥' z → x ≥' z
  _≡⟨_⟩_ : ∀ x {y} → x ≡  y → ∀ {z} → y ≥' z → x ≥' z
  _∎ : ∀ x → x ≥' x

  ℕ▹ℝ : ℕ → ℝ

  sum : Event → ℕ
  sum-ext : {A B : Event} → (∀ r → A r ≡ B r) → sum A ≡ sum B

  sumFin : (q : ℕ) (f : Fin q → ℝ) → ℝ

RndVar = Ω → ℝ

_² : ℝ → ℝ
x ² = x · x

_²' : RndVar → RndVar
(X ²') r = (X r)²

postulate
  E[_] : RndVar → ℝ

  lemma2 : ∀ X → E[ X ²' ] ≥' E[ X ] ²

_≡⟨by-definition⟩_ : ∀ x {z} → x ≥' z → x ≥' z
x ≡⟨by-definition⟩ y = x ≡⟨ refl ⟩ y

-- _/_ : [0,1] → (d : ℕ){{_ : d ≥ 1}} → [0,1]
_/_ : ℝ → (d : ℕ){{_ : d ≥ 1}} → ℝ
x / y = x · 1/ y

Pr : Event → ℝ -- [0,1]
Pr A = ℕ▹ℝ (sum A) / #Ω

Pr-ext : ∀ {A B : Event} → (∀ r → A r ≡ B r) → Pr A ≡ Pr B
Pr-ext f = ap (λ x → ℕ▹ℝ x / #Ω) (sum-ext f)

-- Lemma 1, equation (3)
lemma1-3 : Pr frk ≥' Pr acc · ((Pr acc / q) - (1/ #h))
lemma1-3 = Pr frk
       ≡⟨ {!Pr!} ⟩
         Pr I≥1∧I=I'∧h≢h'
       ≥⟨ {!!} ⟩
         Pr I≥1∧I=I' - Pr I≥1∧h=h'
       ≡⟨ ap (λ x → Pr I≥1∧I=I' - x) {!!} ⟩
         Pr I≥1∧I=I' - (Pr I≥1 / #h)
       ≡⟨by-definition⟩
         Pr I≥1∧I=I' - (Pr acc / #h)
       ≡⟨ {!!} ⟩
         Pr acc · ((Pr acc / q) - (1/ #h))
       ∎

lemma1-4 : Pr I≥1∧I=I' ≥' (Pr acc)² / q
lemma1-4
  = Pr I≥1∧I=I'
  ≡⟨ {!!} ⟩
    sumFin q (λ i → Pr (I=I'=1+ i))
  ≡⟨ {!!} ⟩ -- Conditional probabilities
    sumFin q (λ i → Pr (I=1+ i) · Pr (I=I'=1+ i))
  ≡⟨ {!!} ⟩
    (Pr acc)² / q
  ∎

-- -}
-- -}
-- -}
-- -}
-- -}
