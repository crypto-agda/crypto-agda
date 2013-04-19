module Search.Searchable.Isos where

open import Function
open import Data.Product
open import Data.Nat
open import Data.Vec renaming (sum to vsum)
open import Function.Related.TypeIsomorphisms.NP
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_)

open import Search.Type
open import Search.Searchable
open import Search.Searchable.Product

swap-μ : ∀ {A B} → Searchable (A × B) → Searchable (B × A)
swap-μ = μ-iso swap-iso

swapS-preserve : ∀ {A B} f (μA×B : Searchable (A × B)) → sum μA×B f ≡ sum (swap-μ μA×B) (f ∘ swap)
swapS-preserve = μ-iso-preserve swap-iso

μ^ : ∀ {A} (μA : Searchable A) n → Searchable (A ^ n)
μ^ μA zero    = μLift μ⊤
μ^ μA (suc n) = μA ×-μ μ^ μA n

μVec : ∀ {A} (μA : Searchable A) n  → Searchable (Vec A n)
μVec μA n = μ-iso (^↔Vec n) (μ^ μA n)
