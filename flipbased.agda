module flipbased where

open import Algebra
import Level as L
open L using () renaming (_⊔_ to _L⊔_)
open import Function using (id; _∘_; const; _$_)
open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂; _,_; swap; _×_)
open import Data.Bits hiding (replicateM)
open import Data.Vec using (Vec; []; _∷_; take; drop)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡

record M {a} n (A : Set a) : Set a where
  constructor mk
  field
    run : Bits n → A

flip′ : M 1 Bit
flip′ = mk (λ { (b ∷ []) → b })

return′ : ∀ {a} {A : Set a} → A → M 0 A
return′ x = mk (λ _ → x)

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

weaken≤ : ∀ {m n a} {A : Set a} → n ≤ m → M n A → M m A
weaken≤ p = comap (take≤ p)

flip : ∀ {n} → M (1 + n) Bit
flip = weaken′ flip′

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

replicateM : ∀ {a} {A : Set a} {n m} → M m A → M (n * m) (Vec A n)
replicateM {n = zero}  _ = pure []
replicateM {n = suc n} {m} x rewrite ℕ°.+-comm (n * m) m = pure {0} _∷_ ⊛ x ⊛ replicateM x

flips : ∀ {n} → M n (Bits n)
-- specialized version for now
flips {zero} = pure []
flips {suc n} = map _∷_ flip′ ⊛ flips {n}

_⟨_⟩_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {m n} →
        M m A → (A → B → C) → M n B → M (m + n) C
x ⟨ f ⟩ y = map f x ⊛ y

private --move to Data.Nat.NP
  module ⊔° = CommutativeSemiringWithoutOne ⊔-⊓-0-commutativeSemiringWithoutOne

record ProgEquiv a ℓ : Set (L.suc ℓ L⊔ L.suc a) where
  infix 2 _≈_
  field
    _≈_ : ∀ {n} {A : Set a} → Rel (M n A) ℓ

  _≋_ : ∀ {n₁ n₂} {A : Set a} → M n₁ A → M n₂ A → Set ℓ
  _≋_ {n₁} {n₂} p₁ p₂ = _≈_ {n = n₁ ⊔ n₂} (weaken≤ (m≤m⊔n _ _) p₁) (weaken≤ (m≤n⊔m _ n₁) p₂)
    where m≤n⊔m : ∀ m n → m ≤ n ⊔ m
          m≤n⊔m m n rewrite ⊔°.+-comm n m = m≤m⊔n m n

record PRG (prgEq : ProgEquiv L.zero L.zero) k n : Set where
  open ProgEquiv prgEq
  field
    prg : Bits k → Bits n
    sec : map prg flips ≋ flips

init : ∀ {k a} {A : Set a} → (Bits k → A) → M k A
init f = map f flips

module Examples (progEq : ProgEquiv L.zero L.zero) where
  open ProgEquiv progEq
  ex₁ = ∀ {x} → flip′ ⟨ _xor_ ⟩ pure′ x ≈ pure x

  ex₂ = p ≈ map swap p where p = flip′ ⟨ _,_ ⟩ flip′ 

  ex₃ = ∀ {n} {xs : Bits n} → map (_⊕_ xs) flips ≈ flips

  ex₄ = ∀ {k n} (prg : PRG progEq k n) xs → map (_⊕_ xs ∘ PRG.prg prg) flips ≋ flips
