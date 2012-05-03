module Data.Tree.Binary.Perfect.Any where

open import Level
open import Relation.Binary.PropositionalEquality
open import prefect-bintree

data Any {a p} {A : Set a} (P : A → Set p) : ∀ {n} → Tree A n → Set (a ⊔ p) where
  leaf  : ∀ {x} (Px : P x) → Any P (leaf x)
  left  : ∀ {n} {t₀ t₁ : Tree A n} → Any P t₀ → Any P (fork t₀ t₁)
  right : ∀ {n} {t₀ t₁ : Tree A n} → Any P t₁ → Any P (fork t₀ t₁)

pattern here = Any.leaf

data All {a p} {A : Set a} (P : A → Set p) : ∀ {n} → Tree A n → Set (a ⊔ p) where
  leaf  : ∀ {x} (Px : P x) → All P (leaf x)
  fork  : ∀ {n} {t₀ t₁ : Tree A n} → All P t₀ → All P t₁ → All P (fork t₀ t₁)

_∈_ : ∀ {a} {A : Set a} (x : A) {n} → Tree A n → Set a
x ∈ t = Any (_≡_ x) t

lookup : ∀ x t → Dec (x ∈ t)

P ⇒ Q → All P t → All Q (map f t)
