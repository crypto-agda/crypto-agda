{-# OPTIONS --without-K #-}
module flipbased-tree where

open import Function using (flip)
open import Data.Bits using (Bit; 0b; 1b; Bits)

open import bintree using (leaf; fork; toFun)
open bintree public using (Tree) renaming (map to map↺; join to join↺)
import flipbased
import flipbased-running
import flipbased-counting

-- “↺ n A” reads like: “toss n coins, then return a value of type A”
↺ : ∀ {a} n (A : Set a) → Set a
↺ = flip Tree

return↺ : ∀ {c a} {A : Set a} → A → ↺ c A
return↺ = leaf

runDet : ∀ {a} {A : Set a} → ↺ 0 A → A
runDet (leaf x) = x

toss : ↺ 1 Bit
toss = fork (leaf 0b) (leaf 1b)

run↺ : ∀ {n a} {A : Set a} → ↺ n A → Bits n → A
run↺ = toFun

open flipbased ↺ toss leaf map↺ join↺ public
open flipbased-running ↺ toss return↺ map↺ join↺ run↺ public
open flipbased-counting ↺ toss return↺ map↺ join↺ count↺ public
