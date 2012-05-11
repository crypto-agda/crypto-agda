module otp-sem-sec where

open import Function
open import Data.Nat.NP
open import Data.Bits
open import Data.Bool
open import Data.Vec
open import Data.Product
open import circuit
open import Relation.Binary.PropositionalEquality

-- dup from Game
EXP : ∀ {a b} {A : Set a} {B : Set b} → Bit → (A → B) → (A × A → B)
EXP 0b f (x₀ , x₁) = f x₀
EXP 1b f (x₀ , x₁) = f x₁

Coins = ℕ
Ports = ℕ

module F'
  (|M| |C| : ℕ)

  (Proba : Set)
  (Pr[_≡1] : ∀ {c} (EXP : Bits c → Bit) → Proba)
  (dist : Proba → Proba → Proba)
  (negligible : Proba → Set)

  where

  record Power : Set where
    constructor mk
    field
      coins : Coins
  open Power public

  M = Bits |M|
  C = Bits |C|

  ↺ : Coins → Set → Set
  ↺ c A = Bits c → A

  record SemSecAdv power : Set where
    constructor mk

    open Power power renaming (coins to c)
    field
      {c₀ c₁}   : Coins
      c≡c₀+c₁  : c ≡ c₀ + c₁
      beh : ↺ c₀ ((M × M) × (C → ↺ c₁ Bit))

  -- Returing 0 means Chal wins, Adv looses
  --          1 means Adv  wins, Chal looses
  runSemSec : ∀ (E : M → C) {p} (A : SemSecAdv p) (b : Bit) → ↺ (coins p) Bit
  runSemSec E {mk c} A b R
      = case SemSecAdv.beh A R₀ of λ
          { (m0m1 , kont) → b == kont (EXP b E m0m1) R₁ }
    where R₀ = take (SemSecAdv.c₀ A) (subst Bits (SemSecAdv.c≡c₀+c₁ A) R)
          R₁ = drop (SemSecAdv.c₀ A) (subst Bits (SemSecAdv.c≡c₀+c₁ A) R)

  -- runSemSec : ∀ (E : M → C) {p} (A : SemSecAdv p) (b : Bit) → ↺ (coins p) Bit

  negligible-advantage : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  negligible-advantage EXP = negligible (dist Pr[ EXP 0b ≡1] Pr[ EXP 1b ≡1])

  SemSec : ∀ (E : M → C) → Power → Set
  SemSec E power = ∀ (A : SemSecAdv power) → negligible-advantage (runSemSec E A)

  |K| = |M|
  K = Bits |K|
  -- OTP : K → M → C
  -- OTP = _⊕_

  -- OTP-SemSec : SemSec (OTP 

  Enc = M → C

  Tr = Enc → Enc

  -- In general the power might change
  SemSecTr : Tr → Set
  SemSecTr tr = ∀ {E p} → SemSec (tr E) p → SemSec E p

  neg-pres-sem-sec : SemSecTr (_∘_ vnot)
  neg-pres-sem-sec {E} {p} E'-sec A = A-breaks-E
     where E' : Enc
           E' = vnot ∘ E
           open SemSecAdv A using (c≡c₀+c₁ ; c₀ ; c₁) renaming (beh to A-beh)
           A'-beh : ↺ c₀ ((M × M) × (C → ↺ c₁ Bit))
           A'-beh = {!!}
           A' : SemSecAdv p
           A' = {!!}
           A'-breaks-E' : negligible-advantage (runSemSec E' A')
           A'-breaks-E' = E'-sec A'
           A-breaks-E : negligible-advantage (runSemSec E A)
           A-breaks-E = {!!}

{-
  ⊕-pres-sem-sec : ∀ mask → SemSecTr (_∘_ (_⊕_ mask))
  ⊕-pres-sem-sec mask {E} {p} E-sec A-breaks-E' = pf
     where E' : Enc
           E' = (_⊕_ mask) ∘ E
           pf : negligible-advantage (runSemSec E' A-breaks-E')
           pf = {!!}
-}

module F
  (Size Time : Set)
  (FCp : Coins → Size → Time → Ports → Ports → Set)
  (Cp : Ports → Ports → Set)
  (builder : CircuitBuilder Cp)
  (toC : ∀ {c s t i o} → FCp c s t i o → Cp (c + i) o)
  (runC : ∀ {i o} → Cp i o → Bits i → Bits o)

  (|M| |C| : ℕ)

  (Proba : Set)
  (Pr[_≡1] : ∀ {c} (EXP : Bits c → Bit) → Proba)
  (dist : Proba → Proba → Proba)
  (negligible : Proba → Set)

  where

  record Power : Set where
    constructor mk
    field
      coins : Coins
      size  : Size
      time  : Time
  open Power public

  M = Bits |M|
  C = Bits |C|

  ↺ : Coins → Set → Set
  ↺ c A = Bits c → A

  record SemSecAdv power : Set where
    constructor mk

    open Power power renaming (coins to c; size to s; time to t)
    field
      fcp : FCp c s t |C| (1 + (|M| + |M|))

      {c₀ c₁}   : Coins
      c≡c₀+c₁  : c ≡ c₀ + c₁

    R₀ = Bits c₀
    R₁ = Bits c₁

    open CircuitBuilder builder

    cp : Cp ((c₀ + c₁) + |C|) (1 + (|M| + |M|))
    cp rewrite sym c≡c₀+c₁ = toC fcp

    cp₁ : Cp c₀ (|M| + |M|)
    cp₁ = padR c₁ >>> padR |C| >>> cp >>> tailC

    cp₂ : Cp ((c₀ + c₁) + |C|) 1
    cp₂ = cp >>> headC

    beh : ↺ c₀ ((M × M) × (C → ↺ c₁ Bit))
    beh R₀ = (case splitAt |M| (runC cp₁ R₀) of λ { (x , y , _) → (x , y) })
           , (λ C R₁ → head (runC cp₂ ((R₀ ++ R₁) ++ C)))

  runSemSec : ∀ (E : M → C) {p} (A : SemSecAdv p) (b : Bit) → ↺ (coins p) Bit
  runSemSec E {mk c s t} A b R
      = case SemSecAdv.beh A R₀ of λ
          { (m0m1 , kont) → {- b == -} kont (EXP b E m0m1) R₁ }
    where R₀ = take (SemSecAdv.c₀ A) (subst Bits (SemSecAdv.c≡c₀+c₁ A) R)
          R₁ = drop (SemSecAdv.c₀ A) (subst Bits (SemSecAdv.c≡c₀+c₁ A) R)

  -- runSemSec : ∀ (E : M → C) {p} (A : SemSecAdv p) (b : Bit) → ↺ (coins p) Bit

  negligible-advantage : ∀ {c} (EXP : Bit → ↺ c Bit) → Set
  negligible-advantage EXP = negligible (dist Pr[ EXP 0b ≡1] Pr[ EXP 1b ≡1])

  SemSec : ∀ (E : M → C) → Power → Set
  SemSec E power = ∀ (A : SemSecAdv power) → negligible-advantage (runSemSec E A)

  |K| = |M|
  K = Bits |K|
  -- OTP : K → M → C
  -- OTP = _⊕_

  -- OTP-SemSec : SemSec (OTP 

  Enc = M → C

  Tr = Enc → Enc

  -- In general the power might change
  SemSecTr : Tr → Set
  SemSecTr tr = ∀ {E p} → SemSec (tr E) p → SemSec E p

  neg-pres-sem-sec : SemSecTr (_∘_ vnot)
  neg-pres-sem-sec {E} {p} E'-sec A = A-breaks-E
     where E' : Enc
           E' = vnot ∘ E
           open SemSecAdv A using (c≡c₀+c₁ ; c₀ ; c₁) renaming (beh to A-beh)
           A'-beh : ↺ c₀ ((M × M) × (C → ↺ c₁ Bit))
           A'-beh = {!!}
           A' : SemSecAdv p
           A' = {!!}
           A'-breaks-E' : negligible-advantage (runSemSec E' A')
           A'-breaks-E' = E'-sec A'
           A-breaks-E : negligible-advantage (runSemSec E A)
           A-breaks-E = {!!}

{-
  ⊕-pres-sem-sec : ∀ mask → SemSecTr (_∘_ (_⊕_ mask))
  ⊕-pres-sem-sec mask {E} {p} E-sec A-breaks-E' = pf
     where E' : Enc
           E' = (_⊕_ mask) ∘ E
           pf : negligible-advantage (runSemSec E' A-breaks-E')
           pf = {!!}
-}
