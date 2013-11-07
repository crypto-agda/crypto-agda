open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product
open import Data.One

import Game.IND-CPA-alt
import Game.IND-CCA
import Game.CCA-Common

import Game.Transformation.Naor-Yung

module Game.Transformation.Naor-Yung-proof
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)
  (Proof      : ★)
  

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)
  (Prove  : Message → PubKey → PubKey → Rₑ → Rₑ → CipherText → CipherText → Proof)
  (Verify : (Bit → CipherText) → Proof → Bit)
  (Sim    : (Bit → CipherText) → Proof)
where

module NY = Game.Transformation.Naor-Yung PubKey SecKey Message CipherText Proof Rₑ Rₖ KeyGen Enc Dec Prove Verify

module CPA = Game.IND-CPA-alt PubKey SecKey Message CipherText Rₑ Rₖ (Bit × Rₖ × Rₑ × Rₐ) KeyGen Enc
module CCA = Game.IND-CCA NY.PubKey' NY.SecKey' NY.Message' NY.CipherText' NY.Rₑ' NY.Rₖ' Rₐ NY.KeyGen' NY.Enc' NY.Dec'

swap? : ∀ {X : ★} → Bit → (X × X) → Bit → X
swap? b p i = proj′ p (b xor i) 

transformation : CCA.Adv → CPA.Adv
transformation adv (b' , rₖ , rₑ , rₐ) y = go (adv rₐ pk')
  module transformation where

    y' = proj₁ (KeyGen rₖ)
    x' = proj₂ (KeyGen rₖ)

  
    pk' = swap? b' (y , y')
    
    go : _ → _
    go (Game.CCA-Common.Ask-Oracle (cc , π) x₁) = go (x₁ m?)
      module go-ask where
        m? = [0: nothing 1: just (Dec x' (cc (not b'))) ] (Verify cc π)
    go (Game.CCA-Common.Pick x) = mb , cont
      module go-pick where
        mb = proj′ (proj₁ x)
        cont : _ → Bit
        cont c = proj₂ x (cc' , Sim cc')
          module cont where
            cc' = swap? b' (c , Enc y' (mb b') rₑ)


open import Relation.Binary.PropositionalEquality
            
R = CPA.R × CCA.R
            
thm : ∀ adv cpaR ccaR b → CCA.⅁ b adv ccaR ≡ CPA.⅁ b (transformation adv) cpaR
thm adv cpaR ccaR 1b = {!refl!}
thm adv cpaR ccaR 0b = {!!}
