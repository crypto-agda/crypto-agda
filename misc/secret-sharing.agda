open import Level.NP
open import Algebra
open import Algebra.Structures
open import Type
open import Data.Nat
open import Data.Vec
open import Data.Product
open import Relation.Binary.NP

module secret-sharing where

module AbstractSplitSecret (G : Group ₀ ₀) where

  open Group G renaming (Carrier to M)

  big[∙] : ∀ {n} → Vec M n → M
  big[∙] = foldr _ _∙_ ε

  {-
    n is the number of shares - 1
    s is the secret message
    r is a vector of n random messages
  -}
  split-secret : ∀ {n} (s : M) (r : Vec M n) → Vec M (suc n)
  split-secret s r = (s ∙ (big[∙] r)⁻¹) ∷ r

  merge-shares : ∀ {n} (shares : Vec M (suc n)) → M
  merge-shares = big[∙]

  Correctness = ∀ {n} s (r : Vec M n)
                        → merge-shares (split-secret s r) ≈ s

  secret-sharing-correct : Correctness 
  secret-sharing-correct s r
      = s ∙ (big[∙] r)⁻¹ ∙ big[∙] r
      ≈⟨ assoc _ _ _ ⟩
         s ∙ ((big[∙] r)⁻¹ ∙ big[∙] r)
      ≈⟨ ∙-cong refl (proj₁ inverse _) ⟩
         s ∙ ε
      ≈⟨ proj₂ identity s ⟩
         s
      ∎
      where open Equivalence-Reasoning isEquivalence

open import Data.Two
open import Data.Bits
open import Relation.Binary.PropositionalEquality

module ConcreteXorTwoSplitSecret = AbstractSplitSecret Xor°.+-group
module ConcreteXorBitsSplitSecret n = AbstractSplitSecret (⊕-group n)

module TestTwo where
  open ConcreteXorTwoSplitSecret
  s = 0₂
  x = 1₂
  y = 0₂
  r = x ∷ y ∷ []
  shares = split-secret s r
  test1 : s ≡ merge-shares shares
  test1 = refl
  test2 : s ≡ merge-shares (reverse shares)
  test2 = refl

module TestBits where
  open ConcreteXorBitsSplitSecret 6
  s = 0₂ ∷ 1₂ ∷ 1₂ ∷ 0₂ ∷ 0₂ ∷ 1₂ ∷ []
  x = 1₂ ∷ 1₂ ∷ 1₂ ∷ 1₂ ∷ 0₂ ∷ 0₂ ∷ []
  y = 0₂ ∷ 1₂ ∷ 1₂ ∷ 0₂ ∷ 1₂ ∷ 0₂ ∷ []
  r = x ∷ y ∷ []
  shares = split-secret s r
  test1 : s ≡ merge-shares shares
  test1 = refl
  test2 : s ≡ merge-shares (reverse shares)
  test2 = refl
-- -}
