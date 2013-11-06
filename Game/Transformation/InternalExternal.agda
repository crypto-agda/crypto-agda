-- NOTE with-K
module Game.Transformation.InternalExternal where

open import Data.Two
open import Data.Nat.NP hiding (_==_)
open import Data.Nat.Distance
open import Data.Product

open import Function

open import Explore.Core
open import Explore.Properties
open import Explore.Summable
open import Explore.Sum
open import Explore.Product
open import Explore.Two

open import Relation.Binary.PropositionalEquality.NP

module GameFlipping (R : Set)(sum : Sum R)(sum-ind : SumInd sum)(⅁ : 𝟚 → R → 𝟚) where
  open Operators
  X Y : R → 𝟚
  X = ⅁ 0₂
  Y = ⅁ 1₂
  R' = 𝟚 × R
  sum' : Sum R'
  sum' = 𝟚ˢ ×ˢ sum

  open FromSum    sum'    renaming (count to #'_)
  open FromSumInd sum-ind renaming (count to #_)

  G : R' → 𝟚
--  G (b , r) = b == (case b 0→ X 1→ Y) r
--  G (b , r) = b == (case b 0→ X r 1→ Y r)
  G (b , r) = b == ⅁ b r

  1/2 : R' → 𝟚
  1/2 = proj₁

  -- TODO use the library
  lemma : ∀ X → sum (const 1) ≡ #(not ∘ X) + # X
  lemma X = sum-ind P refl (λ {a}{b} → part1 {a}{b}) part2
    where
      count = FromSum.count

      P = λ s → s (const 1) ≡ count s (not ∘ X) + count s X

      part1 : ∀ {s₀ s₁} → P s₀ → P s₁ → P (λ f → s₀ f + s₁ f)
      part1 {s₀} {s₁} Ps₀ Ps₁ rewrite Ps₀ | Ps₁ = +-interchange (count s₀ (not ∘ X)) (count s₀ X) (count s₁ (not ∘ X)) (count s₁ X)

      part2 : ∀ x → P (λ f → f x)
      part2 x with X x
      part2 x | 0₂ = refl
      part2 x | 1₂ = refl

  thm : dist (#' G) (#' 1/2) ≡ dist (# Y) (# X)
  thm = dist (#' G) (#' 1/2)
      ≡⟨ cong (dist (#' G)) helper ⟩
        dist (#' G) (#(not ∘ X) + # X)
      ≡⟨ refl ⟩ -- #' definition
        dist (# (_==_ 0₂ ∘ X) + # (_==_ 1₂ ∘ Y)) (# (not ∘ X) + # X)
      ≡⟨ refl ⟩ -- #' definition
        dist (# (not ∘ X) + # Y) (# (not ∘ X) + # X)
      ≡⟨ dist-x+ (# (not ∘ X)) (# Y) (# X) ⟩
        dist (# Y) (# X)
      ∎
    where
      open ≡-Reasoning

      helper = #' 1/2
             ≡⟨ refl ⟩
               sum (const 0) + sum (const 1)
             ≡⟨ cong (λ p → p + sum (const 1)) sum-zero ⟩
               sum (const 1)
             ≡⟨ lemma X ⟩
               # (not ∘ X) + # X
             ∎
