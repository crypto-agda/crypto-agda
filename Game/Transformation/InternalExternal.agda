module dist-props where

open import Data.Two
open import Data.Nat.NP hiding (_==_)
open import Data.Product

open import Function

open import Search.Type
open import Search.Sum

open import Search.Searchable.Sum
open import Search.Searchable.Product

open import Relation.Binary.PropositionalEquality.NP

module GameFlipping (R : Set)(sum : Sum R)(sum-ind : SumInd sum)(⅁ : 𝟚 → R → 𝟚) where
  X Y : R → 𝟚
  X = ⅁ 0'
  Y = ⅁ 1'
  R' = 𝟚 × R
  sum' : Sum R'
  sum' = searchBit _+_ ×-sum sum

  open FromSum sum' renaming (count to #'_)
  open FromSumInd sum-ind renaming (count to #_)

  G : R' → 𝟚
--  G (b , r) = b == (case b 0→ X 1→ Y) r
--  G (b , r) = b == (case b 0→ X r 1→ Y r)
  G (b , r) = b == ⅁ b r

  1/2 : R' → 𝟚
  1/2 = proj₁

  -- TODO use the library
  lemma : ∀ X → sum (const 1) ≡ #(not ∘ X) + # X
  lemma X = sum-ind P (λ {a}{b} → part1 {a}{b}) part2
    where
      count = FromSum.count

      P = λ s → s (const 1) ≡ count s (not ∘ X) + count s X

      part1 : ∀ {s₀ s₁} → P s₀ → P s₁ → P (λ f → s₀ f + s₁ f)
      part1 {s₀} {s₁} Ps₀ Ps₁ rewrite Ps₀ | Ps₁ = +-interchange (count s₀ (not ∘ X)) (count s₀ X) (count s₁ (not ∘ X)) (count s₁ X)

      part2 : ∀ x → P (λ f → f x)
      part2 x with X x
      part2 x | 0' = refl
      part2 x | 1' = refl

  thm : dist (#' G) (#' 1/2) ≡ dist (# Y) (# X)
  thm = dist (#' G) (#' 1/2)
      ≡⟨ cong (dist (#' G)) helper ⟩
        dist (#' G) (#(not ∘ X) + # X)
      ≡⟨ refl ⟩ -- #' definition
        dist (# (_==_ 0' ∘ X) + # (_==_ 1' ∘ Y)) (# (not ∘ X) + # X)
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
