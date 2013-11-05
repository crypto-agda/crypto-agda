
{-# OPTIONS --without-K #-}

open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Nat.NP hiding (_==_)
open import Data.Nat.Properties
open import Data.Product
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary.PropositionalEquality

open import Explore.Core
open import Explore.Properties
open import Explore.Explorable renaming (module Explorable₀ to Exp
                                        ; module FromExplore₀ to FE)
open import Explore.Product
open Operators

import Game.IND-CCA2-dagger
import Game.IND-CCA2
import Game.IND-CCA

module Game.Transformation.CCA2-CCA2d
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)
  
where

module CCA2d = Game.IND-CCA2-dagger PubKey SecKey Message CipherText
    Rₑ Rₖ Rₐ KeyGen Enc Dec 
module CCA2 X = Game.IND-CCA2  PubKey SecKey Message CipherText
    Rₑ Rₖ (X × Rₐ) KeyGen Enc Dec

X = Bit × Rₑ

f : PubKey → X
  → (Message × Message) × (CipherText → CipherText → CCA2d.DecRound Bit)
  → (Message × Message) × (CipherText → CCA2d.DecRound Bit)
f pk (t  , rₑ) m = (proj₁ m , λ c → proj₂ m c (Enc pk (proj (proj₁ m) t) rₑ))

A-transform : (adv : CCA2d.Adv) → CCA2.Adv X
A-transform adv (x , rₐ) pk = mapStrategy (f pk x) (adv rₐ pk)


{-

This is not enough for the proof, we are missing:

  * explain why we equate the randomness of the adversary with not b
  * explain why we share the randomness rₑ' with the adversary

Informal proof:

  * the randomness t is either t ≡ b in which case we don't care and get
    advantage ≡ ε'
    or it is t ≡ not b, and we have advantage ≡ ε as shown below.
    Total advantage ≡ (ε' + ε) / 2

  * In the "real" proof we will have two different rₑ', one for the adversary
    and one for the game. The interesting thing is that

    Σ (A × A) (λ (x , _) → f x) ≈ Σ (A × A) (λ (_ , x) → f x)

    or more general we can swap a used randomness with an unused one.
    In this case, LHS doesn't use the randomness of the adversary, so we can
    swap the randomness for the second encryption with the adversaries one.
  
-}

correct : ∀ {rₑ rₑ' rₖ rₐ} b adv
        → CCA2d.⅁  b adv               (rₐ , rₖ , rₑ , rₑ')
        ≡ CCA2.EXP X b (A-transform adv) (((not b , rₑ') , rₐ) , rₖ , rₑ)
correct {rₑ}{rₑ' = ra}{rₖ = r}{rₐ} 1b adv with KeyGen r
... | pk , sk = cong (λ x → runStrategy (Dec sk) (proj₂ x (Enc pk (proj₂ (proj₁ x)) rₑ)))
                     (sym (run-map (Dec sk) (f pk (0b , ra)) (adv rₐ pk)))
correct {rₑ}{rₑ' = ra}{rₖ = r}{rₐ} 0b adv with KeyGen r
... | pk , sk = cong (λ x → runStrategy (Dec sk) (proj₂ x (Enc pk (proj₁ (proj₁ x)) rₑ)))
                     (sym (run-map (Dec sk) (f pk (1b , ra)) (adv rₐ pk)))


module Theorem
  (μₑ : Explore₀ Rₑ)
  (μₖ : Explore₀ Rₖ)
  (μₐ : Explore₀ Rₐ)
  (μₑⁱ : ExploreInd₀ μₑ)
  (μₖⁱ : ExploreInd₀ μₖ)
  (μₐⁱ : ExploreInd₀ μₐ)
  where

  open import Explore.Two
  --open import Rat
  
  μₓ : Explore₀ X
  μₓ = 𝟚ᵉ ×ᵉ μₑ
  
  module CCA2dA = CCA2d.Advantage μₑ μₖ μₐ
  module CCA2A  =  CCA2.Advantage X μₑ μₖ (μₓ ×ᵉ μₐ)

  R' : Set
  R' = Rₑ × Rₑ × Rₑ × Rₖ × Rₐ

  R2 : Set
  R2 = Bit × R'
  
  μR' : Explore₀ R'
  μR' = μₑ ×ᵉ μₑ ×ᵉ μₑ ×ᵉ μₖ ×ᵉ μₐ

  μR'ⁱ : ExploreInd₀ μR'
  μR'ⁱ = μₑⁱ ×ⁱ μₑⁱ ×ⁱ μₑⁱ ×ⁱ μₖⁱ ×ⁱ μₐⁱ
  
  μR2 : Explore₀ R2
  μR2 = 𝟚ᵉ ×ᵉ μR'

  module μR' = Exp μR'ⁱ
  module μR2 = FE μR2
  
  # : ∀ {Y : Set} → Bit → (Bit → Y → R2 → Bit) → Y → ℕ
  # b F adv = μR2.count (F b adv)

  lift-CCA2 : Bit → CCA2.Adv X → R2 → Bit
  lift-CCA2 b adv (rt , re , _ , rea , rk , ra) = 
     CCA2.EXP X b adv (((rt , rea) , ra) , (rk , re)) == b
  lift-CCA2d : Bit → CCA2d.Adv → R2 → Bit
  lift-CCA2d b adv (_ , re , re' , _ , rk , ra) = CCA2d.⅁ b adv (ra , rk , re , re') == b
  
  dbl-thm : ∀ {n} → n + n ≡ 2 * n
  dbl-thm {n} rewrite ℕ°.+-comm n 0 = refl
  
  lemma : ∀ b A+ → # b lift-CCA2d A+ ≤ 2 * # b lift-CCA2 (A-transform A+)
  lemma b A+ = μR2.sum (λ { (_ , re , re' , _ , rk , ra)
                          → ⟦ CCA2d.⅁ b A+ ((ra , rk , re , re')) ⟧  })
             ≡⟨ dbl-thm {μR'.sum _} ⟩ 2 *
               (μR'.sum (λ { (re , re' , _ , rk , ra)
                          → ⟦ CCA2d.⅁ b A+ ((ra , rk , re , re')) ⟧  }))
             ≤⟨ s≤s (s≤s (z≤n {0})) *-mono lem ⟩ 2 *
                μR2.sum (λ { (t , re , _ , rea , rk , ra)
                           → ⟦ CCA2.EXP X b (A-transform A+) (((t , rea) , ra) , rk , re) ⟧})
                ∎
    where
      open ≤-Reasoning
      ⟦_⟧ : Bit → ℕ
      ⟦ x ⟧ = Bit▹ℕ (x == b)

      lem1 : ∀ (f : Rₑ → ℕ) → FE.sum μₑ (λ x → FE.sum μₑ (λ y → f x))
                 ≡ FE.sum μₑ (λ x → FE.sum μₑ (λ y → f y))
      lem1 f = Exp.sum-swap' μₑⁱ {_} {FE.sum μₑ} (Exp.sum-zero μₑⁱ) (Exp.sum-hom μₑⁱ) (λ x y → f x)
      
      lem4 : ∀ b (f : Bit → R' → ℕ) → μR'.sum (f b) + μR'.sum (f (not b)) ≡ μR2.sum (λ { (t , r) → f t r})
      lem4 1b f = ℕ°.+-comm (μR'.sum (f 1b)) (μR'.sum (f 0b))
      lem4 0b f = refl

      lem : μR'.sum (λ { (re , re' , _ , rk , ra)
                       → ⟦ CCA2d.⅁ b A+ ((ra , rk , re , re')) ⟧  })
          ≤ μR2.sum (λ { (t , re , _ , rea , rk , ra)
                       → ⟦ CCA2.EXP X b (A-transform A+) (((t , rea) , ra) , rk , re) ⟧})
      lem = (μR'.sum (λ { (re , re' , _ , rk , ra)
                          → ⟦ CCA2d.⅁ b A+ ((ra , rk , re , re')) ⟧  }))
             ≡⟨ Exp.sum-ext μₑⁱ (λ re →  lem1 (λ re' → _)) ⟩ 
               (μR'.sum (λ { (re , _ , re' , rk , ra)
                          → ⟦ CCA2d.⅁ b A+ ((ra , rk , re , re')) ⟧  }))
             ≡⟨ μR'.sum-ext (λ _ → cong ⟦_⟧ (correct b A+) )⟩
                μR'.sum (λ { (re , _ , rea , rk , ra)
                           → ⟦ CCA2.EXP X b (A-transform A+) (((not b , rea) , ra) , rk , re) ⟧})
             ≤⟨ n≤m+n (μR'.sum (λ { (re , _ , rea , rk , ra)
                     → ⟦ CCA2.EXP X b (A-transform A+) (((b , rea) , ra) , rk , re) ⟧})) _ ⟩ (
                μR'.sum (λ { (re , _ , rea , rk , ra)
                           → ⟦ CCA2.EXP X b (A-transform A+) (((b , rea) , ra) , rk , re) ⟧})
             +  μR'.sum (λ { (re , _ , rea , rk , ra)
                           → ⟦ CCA2.EXP X b (A-transform A+) (((not b , rea) , ra) , rk , re) ⟧}))
             ≡⟨ lem4 b (λ { t (re , _ , rea , rk , ra) → ⟦ CCA2.EXP X b (A-transform A+) (((t , rea) , ra) , rk , re) ⟧ }) ⟩
                μR2.sum (λ { (t , re , _ , rea , rk , ra)
                           → ⟦ CCA2.EXP X b (A-transform A+) (((t , rea) , ra) , rk , re) ⟧})
                ∎

{-

Need to show that they are valid aswell:
This is easy, the adversary we are constructing have only a subset
of the restrictions that the original adversary have

-}



-- -}
-- -}
-- -}
-- -}
-- -}
