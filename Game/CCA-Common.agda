open import Type
open import Data.Bit
open import Data.Product hiding (map)
open import Data.Unit
open import Function

module Game.CCA-Common (Message CipherText Rₓ : ★) where
  data Strategy (X : Set): Set where
    Ask-Oracle : CipherText → (Message → Strategy X) → Strategy X
    Pick       : X → Strategy X

  MessageStrategy = Strategy ((Message × Message) × Rₓ)
  
  CipherStrategy  = Strategy Bit
  
  module _ (P : CipherText → Set) where
    Valid : CipherStrategy → Set
    Valid (Ask-Oracle c₁ x) = P c₁ × (∀ m → Valid (x m))
    Valid (Pick x) = ⊤
    
  module Eval {SecKey : ★}(Dec : SecKey → CipherText → Message) sk where
    eval : ∀ {X} → Strategy X → X
    eval (Ask-Oracle c cont) = eval (cont (Dec sk c))
    eval (Pick x) = x

    evalM : MessageStrategy → (Message × Message) × Rₓ
    evalM = eval
    
    evalC : CipherStrategy → Bit
    evalC = eval
