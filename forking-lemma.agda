{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Function.NP
open import Data.Nat.NP hiding (_==_)
open import Data.Vec
open import Data.Maybe
open import Data.One using (𝟙)
open import Data.Two.Base hiding (_==_)
open import Data.Fin.NP as Fin hiding (_+_; _-_; _≤_)
open import Data.Product.NP
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module forking-lemma where

_≥1 : ∀ {n} → Fin n → 𝟚
zero  ≥1 = 0₂
suc _ ≥1 = 1₂

infix 8 _‼_
_‼_ : ∀ {n a}{A : Set a} → Vec A n → Fin n → A
_‼_ = flip lookup

replace : ∀ {A : Type} {q} (I : Fin q)
            (hs hs' : Vec A q) → Vec A q
replace zero    hs             hs' = hs'
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
  RndAdv : Type -- Coin
  {-RndIG  : Type-}

  -- IG : RndIG → Pub

  q     : ℕ

  instance
    q≥1   : q ≥ 1

  #h     : ℕ
  #h≥2   : #h ≥ 2

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

module M (r : Ω) where
  open Ω r

  F' : (I-1 : Fin q)(σ : Res) → Maybe (Res × Res)
  F' I-1 σ =
    case I=I' ∧ h=h' of λ
    { 1₂ → just (σ , σ')
    ; 0₂ → nothing
    }
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
      I≥1  = not (I == zero)

-- Acceptance event for A
acc : Event
acc r = J ≥1
  where open Ω r
     -- x = IG rIG
        J = fst (A {-x-} hs ρ)

frk : Event
frk r = case M.F r of λ { (just _) → 1₂ ; nothing → 0₂ }

instance
    #h≥1 : #h ≥ 1
    #h≥1 = ℕ≤.trans (s≤s z≤n) #h≥2

infix 0 _≥'_
infixr 2 _≥⟨_⟩_ _≡⟨_⟩_
infix 2 _∎

postulate
  [0,1] : Type
  Pr : Event → [0,1]
  _-_ _·_ : [0,1] → [0,1] → [0,1]
  _≥'_ : [0,1] → [0,1] → Type
  1/_ : (d : ℕ){{_ : d ≥ 1}} → [0,1]

  _≥⟨_⟩_ : ∀ x {y} → x ≥' y → ∀ {z} → y ≥' z → x ≥' z
  _≡⟨_⟩_ : ∀ x {y} → x ≡  y → ∀ {z} → y ≥' z → x ≥' z
  _∎ : ∀ x → x ≥' x

_/_ : [0,1] → (d : ℕ){{_ : d ≥ 1}} → [0,1]
x / y = x · 1/ y

{-
lemma3 : Pr frk ≥' Pr acc · ((Pr acc / q) - (1/ #h))
lemma3 = Pr frk
       ≡⟨ {!!} ⟩
         Pr {!λ r → I=I' r ∧ I≥1 r!}
       ≥⟨ {!!} ⟩
         Pr acc · ((Pr acc / q) - (1/ #h))
       ∎
  where
    open M.F
    -- open M.F' I-1 σ

-- -}
-- -}
-- -}
-- -}
-- -}
