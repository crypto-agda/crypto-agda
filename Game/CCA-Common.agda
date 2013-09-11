open import Type
open import Data.Bit
open import Data.Product hiding (map)
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

module Game.CCA-Common (Message CipherText : ★) where
  data Strategy (X : Set): Set where
    Ask-Oracle : CipherText → (Message → Strategy X) → Strategy X
    Pick       : X → Strategy X

  Follow : ∀ {X Y} → (X → Y) → Strategy X → Strategy Y
  Follow f (Ask-Oracle x x₁) = Ask-Oracle x (λ z → Follow f (x₁ z))
  Follow f (Pick x) = Pick (f x)
    
  module Eval {SecKey : ★}(Dec : SecKey → CipherText → Message) sk where
    eval : ∀ {X} → Strategy X → X
    eval (Ask-Oracle c cont) = eval (cont (Dec sk c))
    eval (Pick x) = x

    eval-Follow : ∀ {X Y}(f : X → Y)(s : Strategy X)
                → eval (Follow f s) ≡ f (eval s)
    eval-Follow f (Ask-Oracle x x₁) = eval-Follow f (x₁ (Dec sk x))
    eval-Follow f (Pick x) = refl
