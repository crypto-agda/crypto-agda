{-# OPTIONS --without-K --copatterns #-}
open import Type
open import Data.Two
open import Data.Maybe
open import Data.Product
open import Data.One
open import Data.Two
open import Control.Strategy renaming (run to runStrategy; map to mapStrategy)

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

import Game.IND-CPA-dagger
import Game.IND-CPA

module Game.Transformation.CPA-CPAd
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ† : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)
  
  where

Rₐ = Rₑ × Rₐ†

module CPA  = Game.IND-CPA        PubKey SecKey Message CipherText Rₑ Rₖ Rₐ  𝟙 KeyGen Enc
module CPA† = Game.IND-CPA-dagger PubKey SecKey Message CipherText Rₑ Rₖ Rₐ† 𝟙 KeyGen Enc

open CPA  using (EXP; R; Adversary; module Adversary)
open CPA† using () renaming (EXP to EXP†; R to R†; Adversary to Adversary†; module Adversary to Adversary†)

R→R† : R → R†
R→R† ((rₑ′ , rₐ†) , rₖ , rₑ , _) = rₐ† , rₖ , rₑ , rₑ′ , _

R†→R : R† → R
R†→R (rₐ† , rₖ , rₑ , rₑ′ , _) = (rₑ′ , rₐ†) , rₖ , rₑ , _

-- inv

[rₑ↔rₑ′]† : R† → R†
[rₑ↔rₑ′]† (rₐ† , rₖ , rₑ , rₑ′ , _) = (rₐ† , rₖ , rₑ′ , rₑ , _)

[rₑ↔rₑ′] : R → R
[rₑ↔rₑ′] ((rₑ′ , rₐ†) , rₖ , rₑ , _) = ((rₑ , rₐ†) , rₖ , rₑ′ , _)

[rₑ↔rₑ′]-inv : ∀ r → [rₑ↔rₑ′] ([rₑ↔rₑ′] r) ≡ r
[rₑ↔rₑ′]-inv r = refl

module Transformations (A† : Adversary†) where

  --open Adversary
  module A† = Adversary† A†
  m†  = A†.m
  b′† = A†.b′

  -- For these three transformations we just forward the messages
  m : Rₐ → PubKey → 𝟚 → Message
  m (_ , rₐ†) = m† rₐ†

{-
  fix[t=_] : (t : 𝟚) → Adversary
  m  fix[t= t ] = m′
  b′ fix[t= t ] (rₑ , rₐ†) pk cb = b′† rₐ† pk cb (Enc pk (m† rₐ† pk t) rₑ)
-}

  fix[t=_] : (t : 𝟚) → Adversary
  fix[t= t ] = record { m = m ; b′ = b′ }
   where
    b′ : ∀ _ _ _ → _
    b′ (rₑ , rₐ†) pk cb = b′† rₐ† pk cb (Enc pk (m† rₐ† pk t) rₑ)

  fix[b=_] : (b : 𝟚) → Adversary
  fix[b= b ] = record { m = m ; b′ = b′ }
   where
    b′ : ∀ _ _ _ → _
    b′ (rₑ , rₐ†) pk ct = b′† rₐ† pk (Enc pk (m† rₐ† pk b) rₑ) ct

  fix[t=]-prop : ∀ b t r → EXP b fix[t= t ] r ≡ EXP† b t A† (R→R† r)
  fix[t=]-prop _ _ _ = refl

  fix[b=]-prop : ∀ b t r → EXP t fix[b= b ] r ≡ EXP† b t A† ([rₑ↔rₑ′]† (R→R† r))
  fix[b=]-prop _ _ _ = refl

open import Relation.Binary.PropositionalEquality
module _
  (Dist : ★)
  (0d : Dist)
  (dist : (f g : R → 𝟚) → Dist)
  (dist-comm : (f g : R → 𝟚) → dist f g ≡ dist g f)
  (dist-≗ : {f g : R → 𝟚} → f ≗ g → dist f g ≡ 0d)
  (Negligible : Dist → ★)
  (0d-Negigible : ∀ {d} → d ≡ 0d → Negligible d)
  (_+Dist_ : Dist → Dist → Dist)
  (+Dist-Negligible : ∀ {x y} → Negligible x → Negligible y → Negligible (x +Dist y))
  (neg-dist-trans : {f g h : R → 𝟚} → Negligible (dist f g) → Negligible (dist g h) → Negligible (dist f h))
  (CPA-secure : ∀ b A → Negligible (dist (EXP b A) (EXP (not b) A)))
  where

  _~_ : (f g : R → 𝟚) → ★
  f ~ g = Negligible (dist f g)

  _~†_ : (f g : R† → 𝟚) → ★
  f ~† g = (f ∘ R→R†) ~ (g ∘ R→R†)

  infixr 5 _∙_
  _∙_ : Transitive _~_
  _∙_ = neg-dist-trans

  !_  : Symmetric _~_
  !_ {f} {g} = subst Negligible (dist-comm f g)

  ≗→~ : {f g : R → 𝟚} → f ≗ g → f ~ g
  ≗→~ {f} {g} f≗g = 0d-Negigible (dist-≗ f≗g)

  module _ (A† : Adversary†)
     (SUI : (f : R → R) (f-iso : f ∘ f ≗ id) (h : R → 𝟚) → (h ∘ f) ~ h)
    where
    open Transformations A†

    CPA†-secure : EXP† 0₂ 1₂ A† ~† EXP† 1₂ 0₂ A†
    CPA†-secure = CPA-secure 0₂ fix[t= 1₂ ]
                ∙ SUI [rₑ↔rₑ′] [rₑ↔rₑ′]-inv _
                ∙ CPA-secure 1₂ fix[b= 1₂ ]
                ∙ ≗→~ (λ r → fix[b=]-prop 1₂ 0₂ r)
                ∙ SUI [rₑ↔rₑ′] [rₑ↔rₑ′]-inv _

-- -}
-- -}
-- -}
-- -}
-- -}
