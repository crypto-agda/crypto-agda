open import Function.Related.TypeIsomorphisms.NP
open import Function.Inverse.NP
open import Data.Maybe.NP
open import Data.Nat

open import Search.Type
open import Search.Searchable
open import Search.Searchable.Sum

module Search.Searchable.Maybe where

μMaybe : ∀ {A} → Searchable A → Searchable (Maybe A)
μMaybe μA = μ-iso (sym Maybe↔⊤⊎) (μ⊤ ⊎-μ μA)

μMaybe^ : ∀ {A} n → Searchable A → Searchable (Maybe^ n A)
μMaybe^ zero    μA = μA
μMaybe^ (suc n) μA = μMaybe (μMaybe^ n μA)
