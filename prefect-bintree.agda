module prefect-bintree where

open import Function
open import Data.Nat
open import Data.Bool
open import Data.Bits

data Tree {a} (A : Set a) : ℕ → Set a where
  leaf : (x : A) → Tree A zero
  fork : ∀ {n} (left right : Tree A n) → Tree A (suc n)

fromFun : ∀ {n a} {A : Set a} → (Bits n → A) → Tree A n
fromFun {zero} f = leaf (f [])
fromFun {suc n} f = fork (fromFun (f ∘ 0∷_)) (fromFun (f ∘ 1∷_))

toFun : ∀ {n a} {A : Set a} → Tree A n → Bits n → A
toFun (leaf x) _ = x
toFun (fork left right) (b ∷ bs) = toFun (if b then right else left) bs

lookup : ∀ {n a} {A : Set a} → Bits n → Tree A n → A
lookup = flip toFun

lookup' : ∀ {m n a} {A : Set a} → Bits m → Tree A (m + n) → Tree A n
lookup' [] t = t
lookup' (b ∷ bs) (fork t t₁) = lookup' bs (if b then t₁ else t)

{-
update' : ∀ {m n a} {A : Set a} → Bits m → Tree A n → Tree A (m + n) → Tree A (m + n)
update' = ?
-}

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Tree A n → Tree B n
map f (leaf x) = leaf (f x)
map f (fork t₀ t₁) = fork (map f t₀) (map f t₁)

open import Relation.Binary
open import Data.Star

data Swp {a} {A : Set a} : ∀ {n} (left right : Tree A n) → Set a where
  left : ∀ {n} {left₀ left₁ right : Tree A n} →
         Swp left₀ left₁ →
         Swp (fork left₀ right) (fork left₁ right)
  right : ∀ {n} {left right₀ right₁ : Tree A n} →
         Swp right₀ right₁ →
         Swp (fork left right₀) (fork left right₁)
  swp₁ : ∀ {n} {left right : Tree A n} →
         Swp (fork left right) (fork right left)
  swp₂ : ∀ {n} {t₀₀ t₀₁ t₁₀ t₁₁ : Tree A n} →
         Swp (fork (fork t₀₀ t₀₁) (fork t₁₀ t₁₁)) (fork (fork t₁₁ t₀₁) (fork t₁₀ t₀₀))

Swp★ : ∀ {a} {A : Set a} {n} (left right : Tree A n) → Set a
Swp★ = Star Swp

Swp-sym : ∀ {n a} {A : Set a} → Symmetric (Swp {A = A} {n})
Swp-sym (left s)  = left (Swp-sym s)
Swp-sym (right s) = right (Swp-sym s)
Swp-sym swp₁      = swp₁
Swp-sym swp₂      = swp₂

data Rot {a} {A : Set a} : ∀ {n} (left right : Tree A n) → Set a where
  leaf : ∀ x → Rot (leaf x) (leaf x)
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
Rot-refl {x = fork _ _} = fork Rot-refl Rot-refl

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
