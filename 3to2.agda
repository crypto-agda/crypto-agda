module 3to2 where

open import Type using (★; ★₁)
open import Function.NP using (id; const; _∘_; Π)
open import Data.Nat.NP
open import Data.Bool.NP renaming (Bool to 𝟚; true to 1b; false to 0b; toℕ to 𝟚▹ℕ)
open import Data.Product
open import Data.Maybe.NP
open import Relation.Binary.PropositionalEquality
open import Search.Type renaming (Search₀ to Explore₀; SearchInd to ExploreInd)
open import Search.Searchable
open import Search.Searchable.Product renaming (_×-search-ind_ to _×-explore-ind_)
open import Search.Searchable.Sum renaming (searchBit-ind to explore𝟚-ind)

record _→⁇_ (A B : ★) : ★ where
  constructor ⟨_∥_⟩
  field
    run    : A → B
    valid? : A → 𝟚

  to→? : A →? B
  to→? x = if valid? x then just (run x) else nothing

data 𝟛 : ★ where
  0t 1t 2t : 𝟛

explore𝟛 : Explore₀ 𝟛
explore𝟛 _∙_ f = f 0t ∙ (f 1t ∙ f 2t)

explore𝟛-ind : ∀ {ℓ} → ExploreInd ℓ explore𝟛
explore𝟛-ind _ _∙_ f = f 0t ∙ (f 1t ∙ f 2t)

module |𝟛| = Searchable₀ explore𝟛-ind
module |𝟛×𝟚| = Searchable₀ (explore𝟛-ind ×-explore-ind explore𝟚-ind)

𝟛▹𝟚 : 𝟛 → 𝟚
𝟛▹𝟚 0t = 0b
𝟛▹𝟚 1t = 1b
𝟛▹𝟚 2t = 0b

𝟛▹𝟚-valid? : 𝟛 → 𝟚
𝟛▹𝟚-valid? 0t = 1b
𝟛▹𝟚-valid? 1t = 1b
𝟛▹𝟚-valid? 2t = 0b

𝟛▹𝟚⁇ : 𝟛 →⁇ 𝟚
𝟛▹𝟚⁇ = ⟨ 𝟛▹𝟚 ∥ 𝟛▹𝟚-valid? ⟩

𝟛▹𝟚? : 𝟛 →? 𝟚
𝟛▹𝟚? 0t = just 0b
𝟛▹𝟚? 1t = just 1b
𝟛▹𝟚? 2t = nothing

-- here success? implies validity
success? : Maybe 𝟚 → 𝟚
success? (just x) = x
success? nothing  = 0b

valid? : Maybe 𝟚 → 𝟚
valid? (just _) = 1b
valid? nothing  = 0b

invalid? : Maybe 𝟚 → 𝟚
invalid? = not ∘ valid?

record Fraction : ★ where
  constructor _/_
  field
    numerator denominator : ℕ
open Fraction public

_≡Frac_ : (x y : Fraction) → ★
_≡Frac_ x y =
  numerator x * denominator y ≡ numerator y * denominator x

{- Pr[A|B] = Pr[A∧B] / Pr[B] = #(A∧B) / #B -}

module FromCount {R : ★} (#_ : (R → 𝟚) → ℕ) where

  module Using→? where

    module _ (f : R →? 𝟚) where

      Pr[success|valid] = # (success? ∘ f) / # (valid? ∘ f)

    module _ (f g : R →? 𝟚) where
      _≈_ = Pr[success|valid] f ≡Frac Pr[success|valid] g 

  module Using→⁇ where

    module _ (f⁇ : R →⁇ 𝟚) where
      {- Pr[A|B] = Pr[A∧B] / Pr[B] = #(A∧B) / #B -}
      module f = _→⁇_ f⁇

      Pr[success|valid] = # f.run / # f.valid?

    module _ (f g : R →⁇ 𝟚) where
      _≈_ = Pr[success|valid] f ≡Frac Pr[success|valid] g

open FromCount |𝟛×𝟚|.count

module Test? where
    open Using→?

    ⅁₀ : 𝟛 × 𝟚 →? 𝟚
    ⅁₀ = 𝟛▹𝟚? ∘ proj₁

    ⅁₁ : 𝟛 × 𝟚 →? 𝟚
    ⅁₁ = just ∘ proj₂

    ⅁₀≈⅁₁ : ⅁₀ ≈ ⅁₁
    ⅁₀≈⅁₁ = refl

module Test⁇ where
    open Using→⁇

    ⅁₀ : 𝟛 × 𝟚 → 𝟚
    ⅁₀ = 𝟛▹𝟚 ∘ proj₁

    ⅁₀-valid? : 𝟛 × 𝟚 → 𝟚
    ⅁₀-valid? = 𝟛▹𝟚-valid? ∘ proj₁

    ⅁₁ : 𝟛 × 𝟚 → 𝟚
    ⅁₁ = proj₂

    ⅁₁-valid? : 𝟛 × 𝟚 → 𝟚
    ⅁₁-valid? _ = 1b

    ⅁₀≈⅁₁ : ⟨ ⅁₀ ∥ ⅁₀-valid? ⟩ ≈ ⟨ ⅁₁ ∥ ⅁₁-valid? ⟩
    ⅁₀≈⅁₁ = refl

-- -}
-- -}
-- -}
-- -}
