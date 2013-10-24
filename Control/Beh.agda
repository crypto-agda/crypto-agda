open import Type
open import Data.One

module Control.Beh where

data Beh (PId E S R I O A : ★) : ★ where
  return : A → Beh PId E S R I O A
  input  : (PId → I → Beh PId E S R I O A) → Beh PId E S R I O A
  output : PId → O → Beh PId E S R I O A → Beh PId E S R I O A
  get    : (S → Beh PId E S R I O A) → Beh PId E S R I O A
  set    : S → Beh PId E S R I O A → Beh PId E S R I O A
  ask    : (E → Beh PId E S R I O A) → Beh PId E S R I O A
  rand   : (R → Beh PId E S R I O A) → Beh PId E S R I O A

module _ {PId E S R I O : ★} where
    end : Beh PId E S R I O 𝟙
    end = return _

module Sim[E=𝟙,R=1] {PId S I O A : ★} where
  E = 𝟙
  R = 𝟙
  Proc = Beh PId E S R I O A
  data _≈_ : (P₀ P₁ : Proc) → ★ where
    input-input :
      ∀ {P₀ P₁ : PId → I → Beh _ _ _ _ _ _ _}
      → (∀ i m → P₀ i m ≈ P₁ i m)
      → input P₀ ≈ input P₁
    output-output :
      ∀ {i m P₀ P₁}
      → P₀ ≈ P₁
      → output i m P₀ ≈ output i m P₁
    return-return :
      ∀ x
      → return x ≈ return x
    nop-ask :
      ∀ {P₀ P₁}
      → P₀ ≈ P₁ _
      → P₀ ≈ ask P₁
    nop-rand :
      ∀ {P₀ P₁}
      → P₀ ≈ P₁ _
      → P₀ ≈ rand P₁
    -- rand rand, ask ask...
