module flipbased-product-implem where

open import Function
open import Data.Bits
open import Data.Nat.NP
open import Data.Nat.Properties
open import Data.Vec
open import Data.Product
open import Data.Unit using (⊤)
open import Relation.Binary.NP
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as ≡
import Data.Fin as Fin
open ≡ using (_≗_; _≡_)
open Fin using (Fin; suc)

import flipbased
import flipbased-counting
import flipbased-running

πBits : ℕ → Set
πBits zero = ⊤
πBits (suc n) = Bit × πBits n

toπBits : ∀ {n} → Bits n → πBits n
toπBits [] = _
toπBits (x ∷ xs) = x , toπBits xs

takeπ : ∀ m {n} → πBits (m + n) → πBits m
takeπ zero xs = _
takeπ (suc m) (x , xs) = x , takeπ m xs

dropπ : ∀ m {n} → πBits (m + n) → πBits n
dropπ zero xs = xs
dropπ (suc m) (_ , xs) = dropπ m xs

-- “↺ n A” reads like: “toss n coins and then return a value of type A”
record ↺ {a} n (A : Set a) : Set a where
  constructor mk
  field
    run↺′ : πBits n → A

  run↺ : Bits n → A
  run↺ = run↺′ ∘ toπBits

open ↺ public

private
  -- If you are not allowed to toss any coin, then you are deterministic.
  Det : ∀ {a} → Set a → Set a
  Det = ↺ 0

runDet : ∀ {a} {A : Set a} → Det A → A
runDet (mk f) = f _

toss : ↺ 1 Bit
toss = mk proj₁

return↺ : ∀ {n a} {A : Set a} → A → ↺ n A
return↺ x = mk (const x)

map↺ : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → ↺ n A → ↺ n B
map↺ f (mk g) = mk (f ∘ g)
-- map↺ f x ≗ x >>=′ (return {0} ∘ f)

join↺₁ : ∀ {n a} {A : Set a} → ↺ 1 (↺ n A) → ↺ (1 + n) A
join↺₁ {n} (mk g) = mk λ {(x , xs) → run↺′ (g (x , _)) xs }

join↺ : ∀ {n₁ n₂ a} {A : Set a} → ↺ n₁ (↺ n₂ A) → ↺ (n₁ + n₂) A
join↺ {n₁} {n₂} (mk g) = mk λ xs → run↺′ (g (takeπ n₁ xs)) (dropπ n₁ xs)
-- join↺ x = x >>= id

comap : ∀ {m n a} {A : Set a} → (πBits n → πBits m) → ↺ m A → ↺ n A
comap f (mk g) = mk (g ∘ f)

{-
private
  take≤ : ∀ {m n} → n ≤ m → πBits m → πBits n
  take≤ z≤n _ = _
  take≤ (s≤s p) (x , xs) = x , take≤ p xs

weaken≤ : ∀ {m n a} {A : Set a} → m ≤ n → ↺ m A → ↺ n A
weaken≤ p = comap (take≤ p)
-}

open flipbased ↺ toss return↺ map↺ join↺ public
open flipbased-running ↺ toss return↺ map↺ join↺ run↺ public
open flipbased-counting ↺ toss return↺ map↺ join↺ count↺ public
