open import Algebra
import Level as L
open L using () renaming (_⊔_ to _L⊔_)
open import Function hiding (_⟨_⟩_)
open import Data.Nat.NP hiding (_==_)
open import Data.Bool
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂; _,_; swap; _×_)
open import Data.Bits
open import Data.Bool
open import Data.Vec using (Vec; []; _∷_; take; drop; head; tail) renaming (map to vmap)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module flipbased
   (↺ : ∀ {a} → ℕ → Set a → Set a)
   (toss : ↺ 1 Bit)
   (return↺ : ∀ {n a} {A : Set a} → A → ↺ n A)
   (map↺ : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → ↺ n A → ↺ n B)
   (join↺ : ∀ {n₁ n₂ a} {A : Set a} → ↺ n₁ (↺ n₂ A) → ↺ (n₁ + n₂) A)
 where

Coins = ℕ

-- If you are not allowed to toss any coin, then you are deterministic.
Det : ∀ {a} → Set a → Set a
Det = ↺ 0

-- An experiment
EXP : ℕ → Set
EXP n = ↺ n Bit

-- A guessing game
⅁? : ∀ c → Set
⅁? c = Bit → EXP c

returnᴰ : ∀ {a} {A : Set a} → A → Det A
returnᴰ = return↺

pureᴰ : ∀ {a} {A : Set a} → A → Det A
pureᴰ = returnᴰ

coerce : ∀ {m n a} {A : Set a} → m ≡ n → ↺ m A → ↺ n A
coerce ≡.refl = id

_>>=_ : ∀ {n₁ n₂ a b} {A : Set a} {B : Set b} →
       ↺ n₁ A → (A → ↺ n₂ B) → ↺ (n₁ + n₂) B
_>>=_ x f = join↺ (map↺ f x)

_=<<_ : ∀ {n₁ n₂ a b} {A : Set a} {B : Set b} →
       (A → ↺ n₁ B) → ↺ n₂ A → ↺ (n₁ + n₂) B
_=<<_ {n₁} {n₂} rewrite ℕ°.+-comm n₁ n₂ = flip _>>=_

_>>_ : ∀ {n₁ n₂ a b} {A : Set a} {B : Set b} →
       ↺ n₁ A → ↺ n₂ B → ↺ (n₁ + n₂) B
_>>_ {n₁} x y = x >>= const y

_>=>_ : ∀ {n₁ n₂ a b c} {A : Set a} {B : Set b} {C : Set c}
        → (A → ↺ n₁ B) → (B → ↺ n₂ C) → A → ↺ (n₁ + n₂) C
(f >=> g) x = f x >>= g

weaken : ∀ m {n a} {A : Set a} → ↺ n A → ↺ (m + n) A
weaken m x = return↺ {m} 0 >> x

weaken′ : ∀ {m n a} {A : Set a} → ↺ n A → ↺ (n + m) A
weaken′ x = x >>= return↺

weaken≤ : ∀ {m n a} {A : Set a} → m ≤ n → ↺ m A → ↺ n A
weaken≤ pf x with ≤⇒∃ pf
... | k , ≡.refl = weaken′ x

pure↺ : ∀ {n a} {A : Set a} → A → ↺ n A
pure↺ = return↺

-- Weakened version of toss
tossᵂ : ∀ {n} → ↺ (1 + n) Bit
tossᵂ = toss >>= return↺

_▹↺_ : ∀ {n a b} {A : Set a} {B : Set b} → ↺ n A → (A → B) → ↺ n B
x ▹↺ f = map↺ f x

⟪_⟫ : ∀ {n} {a} {A : Set a} → A → ↺ n A
⟪_⟫ = pure↺

⟪_⟫ᴰ : ∀ {a} {A : Set a} → A → Det A
⟪_⟫ᴰ = pureᴰ

⟪_·_⟫ : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B) → ↺ n A → ↺ n B
⟪ f · x ⟫ = map↺ f x

infixl 4 _⊛_
_⊛_ : ∀ {n₁ n₂ a b} {A : Set a} {B : Set b} →
       ↺ n₁ (A → B) → ↺ n₂ A → ↺ (n₁ + n₂) B
_⊛_ {n₁} mf mx = mf >>= λ f → ⟪ f · mx ⟫ 

⟪_·_·_⟫ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {m n} →
            (A → B → C) → ↺ m A → ↺ n B → ↺ (m + n) C
⟪ f · x · y ⟫ = map↺ f x ⊛ y

⟪_·_·_·_⟫ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {m n o} →
              (A → B → C → D) → ↺ m A → ↺ n B → ↺ o C → ↺ (m + n + o) D
⟪ f · x · y · z ⟫ = map↺ f x ⊛ y ⊛ z

choose : ∀ {n a} {A : Set a} → ↺ n A → ↺ n A → ↺ (suc n) A
choose x y = toss >>= λ b → if b then x else y

zip↺ : ∀ {c₀ c₁ a b} {A : Set a} {B : Set b} → ↺ c₀ A → ↺ c₁ B → ↺ (c₀ + c₁) (A × B)
zip↺ x y = ⟪ _,_ · x · y ⟫

_⟨,⟩_ : ∀ {a b} {A : Set a} {B : Set b} {m n} → ↺ m A → ↺ n B → ↺ (m + n) (A × B)
_⟨,⟩_ = zip↺

_⟨xor⟩_ : ∀ {n₁ n₂} → ↺ n₁ Bit → ↺ n₂ Bit → ↺ (n₁ + n₂) Bit
x ⟨xor⟩ y = ⟪ _xor_ · x · y ⟫

_⟨⊕⟩_ : ∀ {n₁ n₂ m} → ↺ n₁ (Bits m) → ↺ n₂ (Bits m) → ↺ (n₁ + n₂) (Bits m)
x ⟨⊕⟩ y = ⟪ _⊕_ · x · y ⟫

_⟨==⟩_ : ∀ {n₁ n₂ m} → ↺ n₁ (Bits m) → ↺ n₂ (Bits m) → ↺ (n₁ + n₂) Bit
x ⟨==⟩ y = ⟪ _==_ · x · y ⟫

T↺ : ∀ {k} → ↺ k Bit → ↺ k Set
T↺ p = ⟪ T · p ⟫

replicate↺ : ∀ {n m} {a} {A : Set a} → ↺ m A → ↺ (n * m) (Vec A n)
replicate↺ {zero}  _ = ⟪ [] ⟫
replicate↺ {suc _} x = ⟪ _∷_ · x · replicate↺ x ⟫

random : ∀ {n} → ↺ n (Bits n)
-- random = coerce ? (replicate↺ toss) -- specialized version for now to avoid coerce
random {zero}  = ⟪ [] ⟫
random {suc _} = ⟪ _∷_ · toss · random ⟫

randomTbl : ∀ m n → ↺ (2 ^ m * n) (Vec (Bits n) (2 ^ m))
randomTbl m n = replicate↺ random

randomFun : ∀ m n → ↺ (2 ^ m * n) (Bits m → Bits n)
randomFun m n = ⟪ funFromTbl · randomTbl m n ⟫

randomFunExt : ∀ {n k a} {A : Set a} → ↺ k (Bits n → A) → ↺ (k + k) (Bits (suc n) → A)
randomFunExt f = ⟪ comb · f · f ⟫ where comb = λ g₁ g₂ xs → (if head xs then g₁ else g₂) (tail xs)

costRndFun : ℕ → ℕ → ℕ
costRndFun zero n = n
costRndFun (suc m) n = 2* (costRndFun m n)

costRndFun-lem : ∀ m n → costRndFun m n ≡ 2 ^ m * n
costRndFun-lem zero n rewrite ℕ°.+-comm n 0 = ≡.refl
costRndFun-lem (suc m) n rewrite costRndFun-lem m n | ℕ°.*-assoc 2 (2 ^ m) n | ℕ°.+-comm (2 ^ m * n) 0 = ≡.refl

randomFun′ : ∀ {m n} → ↺ (costRndFun m n) (Bits m → Bits n)
randomFun′ {zero}  = ⟪ const · random ⟫
randomFun′ {suc m} = randomFunExt (randomFun′ {m})

record ProgEquiv a ℓ : Set (L.suc ℓ L⊔ L.suc a) where
  infix 2 _≈_ _≋_
  field
    _≈_ : ∀ {n} {A : Set a} → Rel (↺ n A) ℓ

    refl  : ∀ {n A} → Reflexive {A = ↺ n A} _≈_
    sym   : ∀ {n A} → Symmetric {A = ↺ n A} _≈_

    -- not strictly transitive

  reflexive : ∀ {n A} → _≡_ ⇒ _≈_ {n} {A}
  reflexive ≡.refl = refl

  _≋_ : ∀ {n₁ n₂} {A : Set a} → ↺ n₁ A → ↺ n₂ A → Set ℓ
  _≋_ {n₁} {n₂} p₁ p₂ = _≈_ {n = n₁ ⊔ n₂} (weaken≤ (m≤m⊔n _ _) p₁) (weaken≤ (m≤n⊔m _ n₁) p₂)
    where m≤n⊔m : ∀ m n → m ≤ n ⊔ m
          m≤n⊔m m n rewrite ⊔°.+-comm n m = m≤m⊔n m n

  -- Another name for _≋_
  _looks_ : ∀ {n₁ n₂} {A : Set a} → ↺ n₁ A → ↺ n₂ A → Set ℓ
  _looks_ = _≋_

module WithEquiv (progEq : ProgEquiv L.zero L.zero) where
  open ProgEquiv progEq

  SecPRG : ∀ {k n} (prg : (key : Bits k) → Bits n) → Set
  SecPRG prg = this looks random where this = ⟪ prg · random ⟫

  record PRG k n : Set where
    constructor _,_
    field
      prg : Bits k → Bits n
      sec : SecPRG prg

  OneTimeSecPRF : ∀ {k m n} (prf : (key : Bits k) (msg : Bits m) → Bits n) → Set
  OneTimeSecPRF prf = ∀ {xs} → let this = ⟪ prf · random · ⟪ xs ⟫ᴰ ⟫ in
                                this looks random

  record PRF k m n : Set where
    constructor _,_
    field
      prf : Bits k → Bits m → Bits n
      sec : OneTimeSecPRF prf

OTP : ∀ {n} → Bits n → Bits n → Bits n
OTP key msg = key ⊕ msg

init : ∀ {k a} {A : Set a} → (Bits k → A) → ↺ k A
init f = ⟪ f · random ⟫

module Examples (progEq : ProgEquiv L.zero L.zero) where
  open ProgEquiv progEq
  open WithEquiv progEq

  left-unit-law = ∀ {A B : Set} {n} {x : A} {f : A → ↺ n B} → returnᴰ x >>= f ≈ f x

  right-unit-law = ∀ {A : Set} {n} {x : ↺ n A} → returnᴰ =<< x ≈ x

  assoc-law = ∀ {A B C : Set} {n₁ n₂ n₃} {x : ↺ n₁ A} {f : A → ↺ n₂ B} {g : B → ↺ n₃ C}
              → (x >>= f) >>= g ≋ x >>= (λ x → f x >>= g)

  assoc-law′ = ∀ {A B C : Set} {n₁ n₂ n₃} {x : ↺ n₁ A} {f : A → ↺ n₂ B} {g : B → ↺ n₃ C}
              → (x >>= f) >>= g ≈ coerce (≡.sym (ℕ°.+-assoc n₁ n₂ n₃)) (x >>= (λ x → f x >>= g))

  ex₁ = ∀ {x} → toss ⟨xor⟩ ⟪ x ⟫ᴰ ≈ ⟪ x ⟫

  ex₂ = p ≈ map↺ swap p where p = toss ⟨,⟩ toss

  ex₃ = ∀ {n} → OneTimeSecPRF {n} OTP

  ex₄ = ∀ {k n} (prg : PRG k n) → OneTimeSecPRF (λ key xs → xs ⊕ PRG.prg prg key)

  ex₅ = ∀ {k n} → PRG k n → PRF k n n
