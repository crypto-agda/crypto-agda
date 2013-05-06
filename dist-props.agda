module dist-props where

open import Data.Bool.NP
open import Data.Nat.NP hiding (_==_)
open import Data.Product

open import Function

open import Search.Type
open import Search.Sum

open import Search.Searchable.Sum
open import Search.Searchable.Product

open import Relation.Binary.PropositionalEquality.NP

module GameFlipping (R : Set)(sum : Sum R)(sum-ind : SumInd sum)(X Y : R → Bool) where

  R' = Bool × R
  sum' : Sum R'
  sum' = searchBit _+_ ×-sum sum

  open FromSum sum' renaming (count to count')
  open FromSumInd sum-ind

  _==ᴮ_ : Bool → Bool → Bool
  true  ==ᴮ y = y
  false ==ᴮ y = not y

  G : R' → Bool
  G (b , r) = b == (if b then X r else Y r)

  1/2 : R' → Bool
  1/2 = proj₁

  -- TODO use the library
  lemma : ∀ X → sum (const 1) ≡ count (not ∘ X) + count X
  lemma X = sum-ind P (λ {a}{b} → part1 {a}{b}) part2
    where
      # = FromSum.count

      P = λ s → s (const 1) ≡ # s (not ∘ X) + # s X

      part1 : ∀ {s₀ s₁} → P s₀ → P s₁ → P (λ f → s₀ f + s₁ f)
      part1 {s₀} {s₁} Ps₀ Ps₁ rewrite Ps₀ | Ps₁ = +-interchange (# s₀ (not ∘ X)) (# s₀ X) (# s₁ (not ∘ X)) (# s₁ X)

      part2 : ∀ x → P (λ f → f x)
      part2 x with X x
      part2 x | true  = refl
      part2 x | false = refl


  thm : dist (count' G) (count' 1/2) ≡ dist (count X) (count Y)
  thm = dist (count' G) (count' 1/2)
      ≡⟨ cong (dist (count' G)) helper ⟩
        dist (count' G) (count (not ∘ Y) + count Y)
      ≡⟨ refl ⟩ -- count' definition
        dist (count (_==_ false ∘ Y) + count (_==_ true ∘ X)) (count (not ∘ Y) + count Y)
      ≡⟨ {!refl!} ⟩ -- count' definition
        dist (count (not ∘ Y) + count X) (count (not ∘ Y) + count Y)
      ≡⟨ dist-x+ (count (not ∘ Y)) (count X) (count Y) ⟩
        dist (count X) (count Y)
      ∎
    where
      open ≡-Reasoning

      helper = count' 1/2
             ≡⟨ refl ⟩
               sum (const 0) + sum (const 1)
             ≡⟨ cong (λ p → p + sum (const 1)) sum-zero ⟩
               sum (const 1)
             ≡⟨ lemma Y ⟩
               count (not ∘ Y) + count Y
             ∎
