module flipbased where

open import Algebra
import Level as L
open L using () renaming (_⊔_ to _L⊔_)
open import Function hiding (_⟨_⟩_)
open import Data.Nat.NP
open import Data.Bool
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂; _,_; swap; _×_)
open import Data.Bits hiding (replicateM)
open import Data.Bool
open import Data.Vec using (Vec; []; _∷_; take; drop; head; tail)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

record M {a} n (A : Set a) : Set a where
  constructor mk
  field
    run : Bits n → A

toss′ : M 1 Bit
toss′ = mk head

return′ : ∀ {a} {A : Set a} → A → M 0 A
return′ = mk ∘ const

pure′ : ∀ {a} {A : Set a} → A → M 0 A
pure′ = return′

comap : ∀ {m n a} {A : Set a} → (Bits n → Bits m) → M m A → M n A
comap f (mk g) = mk (g ∘ f)

weaken : ∀ {m n a} {A : Set a} → M n A → M (m + n) A
weaken {m} = comap (drop m)

weaken′ : ∀ {m n a} {A : Set a} → M n A → M (n + m) A
weaken′ = comap (take _)

private
  take≤ : ∀ {a} {A : Set a} {m n} → n ≤ m → Vec A m → Vec A n
  take≤ z≤n _ = []
  take≤ (s≤s p) (x ∷ xs) = x ∷ take≤ p xs

weaken≤ : ∀ {m n a} {A : Set a} → m ≤ n → M m A → M n A
weaken≤ p = comap (take≤ p)

coerce : ∀ {m n a} {A : Set a} → m ≡ n → M m A → M n A
coerce ≡.refl = id

toss : ∀ {n} → M (1 + n) Bit
toss = weaken′ toss′

return : ∀ {n a} {A : Set a} → A → M n A
return = weaken′ ∘ return′

pure : ∀ {n a} {A : Set a} → A → M n A
pure = return

_>>=_ : ∀ {n₁ n₂ a b} {A : Set a} {B : Set b} →
       M n₁ A → (A → M n₂ B) → M (n₁ + n₂) B
_>>=_ {n₁} x f = mk (λ bs → M.run (f (M.run x (take _ bs))) (drop n₁ bs))

_>>=′_ : ∀ {n₁ n₂ a b} {A : Set a} {B : Set b} →
       M n₁ A → (A → M n₂ B) → M (n₂ + n₁) B
_>>=′_ {n₁} {n₂} rewrite ℕ°.+-comm n₂ n₁ = _>>=_

_>>_ : ∀ {n₁ n₂ a b} {A : Set a} {B : Set b} →
       M n₁ A → M n₂ B → M (n₁ + n₂) B
_>>_ {n₁} x y = x >>= const y

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → M n A → M n B
map f x = mk (f ∘ M.run x)
-- map f x ≗ x >>=′ (return {0} ∘ f)

join : ∀ {n₁ n₂ a} {A : Set a} →
       M n₁ (M n₂ A) → M (n₁ + n₂) A
join x = x >>= id

infixl 4 _⊛_
_⊛_ : ∀ {n₁ n₂ a b} {A : Set a} {B : Set b} →
       M n₁ (A → B) → M n₂ A → M (n₁ + n₂) B
_⊛_ {n₁} mf mx = mf >>= λ f → map (_$_ f) mx 

_⟨_⟩_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {m n} →
        M m A → (A → B → C) → M n B → M (m + n) C
x ⟨ f ⟩ y = map f x ⊛ y

⟪_⟫ : ∀ {n} {a} {A : Set a} → A → M n A
⟪_⟫ = pure

⟪_⟫′ : ∀ {a} {A : Set a} → A → M 0 A
⟪_⟫′ = pure′

⟪_·_⟫ : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B) → M n A → M n B
⟪ f · x ⟫ = map f x

⟪_·_·_⟫ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {m n} →
            (A → B → C) → M m A → M n B → M (m + n) C
⟪ f · x · y ⟫ = map f x ⊛ y

⟪_·_·_·_⟫ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {m n o} →
              (A → B → C → D) → M m A → M n B → M o C → M (m + n + o) D
⟪ f · x · y · z ⟫ = map f x ⊛ y ⊛ z

choose : ∀ {n a} {A : Set a} → M n A → M n A → M (suc n) A
choose x y = ⟪ if_then_else_ · toss · x · y ⟫

_⟨,⟩_ : ∀ {a b} {A : Set a} {B : Set b} {m n} → M m A → M n B → M (m + n) (A × B)
x ⟨,⟩ y = ⟪ _,_ · x · y ⟫

_⟨xor⟩_ : ∀ {n₁ n₂} → M n₁ Bit → M n₂ Bit → M (n₁ + n₂) Bit
x ⟨xor⟩ y = ⟪ _xor_ · x · y ⟫

_⟨⊕⟩_ : ∀ {n₁ n₂ m} → M n₁ (Bits m) → M n₂ (Bits m) → M (n₁ + n₂) (Bits m)
x ⟨⊕⟩ y = ⟪ _⊕_ · x · y ⟫

replicateM : ∀ {n m} {a} {A : Set a} → M m A → M (n * m) (Vec A n)
replicateM {zero}  _ = ⟪ [] ⟫
replicateM {suc _} x = ⟪ _∷_ · x · replicateM x ⟫

random : ∀ {n} → M n (Bits n)
-- random = coerce ? (replicateM toss) -- specialized version for now to avoid coerce
random {zero}  = ⟪ [] ⟫
random {suc _} = ⟪ _∷_ · toss′ · random ⟫

randomTbl : ∀ m n → M (2 ^ m * n) (Vec (Bits n) (2 ^ m))
randomTbl m n = replicateM random

randomFun : ∀ m n → M (2 ^ m * n) (Bits m → Bits n)
randomFun m n = ⟪ funFromTbl · randomTbl m n ⟫

randomFunExt : ∀ {n k a} {A : Set a} → M k (Bits n → A) → M (k + k) (Bits (suc n) → A)
randomFunExt f = ⟪ comb · f · f ⟫ where comb = λ g₁ g₂ xs → (if head xs then g₁ else g₂) (tail xs)

2*_ : ℕ → ℕ
2* x = x + x

2^_ : ℕ → ℕ
2^ 0       = 1
2^ (suc n) = 2* (2^ n)

costRndFun : ℕ → ℕ → ℕ
costRndFun zero n = n
costRndFun (suc m) n = 2* (costRndFun m n)

lem : ∀ m n → costRndFun m n ≡ 2 ^ m * n
lem zero n rewrite ℕ°.+-comm n 0 = ≡.refl
lem (suc m) n rewrite lem m n | ℕ°.*-assoc 2 (2 ^ m) n | ℕ°.+-comm (2 ^ m * n) 0 = ≡.refl

randomFun′ : ∀ {m n} → M (costRndFun m n) (Bits m → Bits n)
randomFun′ {zero}  = ⟪ const · random ⟫
randomFun′ {suc m} = randomFunExt (randomFun′ {m})

record ProgEquiv a ℓ : Set (L.suc ℓ L⊔ L.suc a) where
  infix 2 _≈_ _≋_
  field
    _≈_ : ∀ {n} {A : Set a} → Rel (M n A) ℓ

    refl  : ∀ {n A} → Reflexive {A = M n A} _≈_
    sym   : ∀ {n A} → Symmetric {A = M n A} _≈_

    -- not strictly transitive

  reflexive : ∀ {n A} → _≡_ ⇒ _≈_ {n} {A}
  reflexive ≡.refl = refl

  _≋_ : ∀ {n₁ n₂} {A : Set a} → M n₁ A → M n₂ A → Set ℓ
  _≋_ {n₁} {n₂} p₁ p₂ = _≈_ {n = n₁ ⊔ n₂} (weaken≤ (m≤m⊔n _ _) p₁) (weaken≤ (m≤n⊔m _ n₁) p₂)
    where m≤n⊔m : ∀ m n → m ≤ n ⊔ m
          m≤n⊔m m n rewrite ⊔°.+-comm n m = m≤m⊔n m n

  -- Another name for _≋_
  _looks_ : ∀ {n₁ n₂} {A : Set a} → M n₁ A → M n₂ A → Set ℓ
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
  OneTimeSecPRF prf = ∀ {xs} → let this = ⟪ prf · random · ⟪ xs ⟫′ ⟫ in
                                this looks random

  record PRF k m n : Set where
    constructor _,_
    field
      prf : Bits k → Bits m → Bits n
      sec : OneTimeSecPRF prf

OTP : ∀ {n} → Bits n → Bits n → Bits n
OTP key msg = key ⊕ msg

init : ∀ {k a} {A : Set a} → (Bits k → A) → M k A
init f = ⟪ f · random ⟫

module Examples (progEq : ProgEquiv L.zero L.zero) where
  open ProgEquiv progEq
  open WithEquiv progEq

  left-unit-law = ∀ {A B : Set} {n} {x : A} {f : A → M n B} → return′ x >>= f ≈ f x

  right-unit-law = ∀ {A : Set} {n} {x : M n A} → x >>=′ return′ ≈ x

  assoc-law = ∀ {A B C : Set} {n₁ n₂ n₃} {x : M n₁ A} {f : A → M n₂ B} {g : B → M n₃ C}
              → (x >>= f) >>= g ≋ x >>= (λ x → f x >>= g)

  assoc-law′ = ∀ {A B C : Set} {n₁ n₂ n₃} {x : M n₁ A} {f : A → M n₂ B} {g : B → M n₃ C}
              → (x >>= f) >>= g ≈ coerce (≡.sym (ℕ°.+-assoc n₁ n₂ n₃)) (x >>= (λ x → f x >>= g))

  ex₁ = ∀ {x} → toss′ ⟨xor⟩ ⟪ x ⟫′ ≈ ⟪ x ⟫

  ex₂ = p ≈ map swap p where p = toss′ ⟨,⟩ toss′

  ex₃ = ∀ {n} → OneTimeSecPRF {n} OTP

  ex₄ = ∀ {k n} (prg : PRG k n) → OneTimeSecPRF (λ key xs → xs ⊕ PRG.prg prg key)

  ex₅ = ∀ {k n} → PRG k n → PRF k n n
