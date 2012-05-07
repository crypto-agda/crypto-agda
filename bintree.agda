module bintree where

open import Function
open import Data.Nat
open import Data.Bool
open import Data.Bits
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

data Tree {a} (A : Set a) : ℕ → Set a where
  leaf : ∀ {n} → A → Tree A n
  fork : ∀ {n} (left right : Tree A n) → Tree A (suc n)

fromFun : ∀ {n a} {A : Set a} → (Bits n → A) → Tree A n
fromFun {zero} f = leaf (f [])
fromFun {suc n} f = fork (fromFun (f ∘ 0∷_)) (fromFun (f ∘ 1∷_))

toFun : ∀ {n a} {A : Set a} → Tree A n → Bits n → A
toFun (leaf x) _ = x
toFun (fork left right) (b ∷ bs) = toFun (if b then right else left) bs

toFun∘fromFun : ∀ {n a} {A : Set a} (f : Bits n → A) → toFun (fromFun f) ≗ f
toFun∘fromFun {zero}  f []        = refl
toFun∘fromFun {suc n} f (0b ∷ bs) = toFun∘fromFun {n} (f ∘ 0∷_) bs
toFun∘fromFun {suc n} f (1b ∷ bs) = toFun∘fromFun {n} (f ∘ 1∷_) bs

leafⁿ : ∀ {n a} {A : Set a} → A → Tree A n
leafⁿ {zero}  x = leaf x
leafⁿ {suc n} x = fork t t where t = leafⁿ x

expand : ∀ {n a} {A : Set a} → Tree A n → Tree A n
expand (leaf x) = leafⁿ x
expand (fork t₀ t₁) = fork (expand t₀) (expand t₁)

fromConst≡leafⁿ : ∀ {n a} {A : Set a} (x : A) → fromFun (const x) ≡ leafⁿ {n} x
fromConst≡leafⁿ {zero}  _ = refl
fromConst≡leafⁿ {suc n} x rewrite fromConst≡leafⁿ {n} x = refl

fromFun∘toFun : ∀ {n a} {A : Set a} (t : Tree A n) → fromFun (toFun t) ≡ expand t
fromFun∘toFun (leaf x) = fromConst≡leafⁿ x
fromFun∘toFun (fork t₀ t₁) = cong₂ fork (fromFun∘toFun t₀) (fromFun∘toFun t₁)

lookup : ∀ {n a} {A : Set a} → Bits n → Tree A n → A
lookup = flip toFun

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Tree A n → Tree B n
map f (leaf x) = leaf (f x)
map f (fork t₀ t₁) = fork (map f t₀) (map f t₁)

data Rot {a} {A : Set a} : ∀ {n} (left right : Tree A n) → Set a where
  leaf : ∀ {n} x → Rot {n = n} (leaf x) (leaf x)
  fork : ∀ {n} {left₀ left₁ right₀ right₁ : Tree A n} →
         Rot left₀ left₁ →
         Rot right₀ right₁ →
         Rot (fork left₀ right₀) (fork left₁ right₁)
  krof : ∀ {n} {left₀ left₁ right₀ right₁ : Tree A n} →
         Rot left₀ right₁ →
         Rot right₀ left₁ →
         Rot (fork left₀ right₀) (fork left₁ right₁)

Rot-refl : ∀ {n a} {A : Set a} → Reflexive (Rot {A = A} {n})
Rot-refl {x = leaf x} = leaf x
Rot-refl {x = fork left right} = fork Rot-refl Rot-refl

Rot-sym : ∀ {n a} {A : Set a} → Symmetric (Rot {A = A} {n})
Rot-sym (leaf x) = leaf x
Rot-sym (fork p₀ p₁) = fork (Rot-sym p₀) (Rot-sym p₁)
Rot-sym (krof p₀ p₁) = krof (Rot-sym p₁) (Rot-sym p₀)

Rot-trans : ∀ {n a} {A : Set a} → Transitive (Rot {A = A} {n})
Rot-trans (leaf x) q = q
Rot-trans (fork p₀ p₁) (fork q₀ q₁) = fork (Rot-trans p₀ q₀) (Rot-trans p₁ q₁)
Rot-trans (fork p₀ p₁) (krof q₀ q₁) = krof (Rot-trans p₀ q₀) (Rot-trans p₁ q₁)
Rot-trans (krof p₀ p₁) (fork q₀ q₁) = krof (Rot-trans p₀ q₁) (Rot-trans p₁ q₀)
Rot-trans (krof p₀ p₁) (krof q₀ q₁) = fork (Rot-trans p₀ q₁) (Rot-trans p₁ q₀)
