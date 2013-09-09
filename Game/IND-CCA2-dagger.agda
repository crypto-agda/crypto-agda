
open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product


open import Relation.Binary.PropositionalEquality

module Game.IND-CCA2-dagger
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ Rₐ Rₐ' Rₓ : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)

where
open import Game.CCA-Common Message CipherText Rₓ
                         
AdvStep₀ : ★
AdvStep₀ = Rₐ → PubKey → MessageStrategy

AdvStep₁ : ★
AdvStep₁ = Rₐ' → Rₓ → PubKey → (c c' : CipherText) → CipherStrategy

Adv : ★
Adv = AdvStep₀ × AdvStep₁

Valid-Adv : Adv → Set
Valid-Adv (m , d) = ∀ {rₐ rₓ pk c c'} → Valid (λ x → x ≢ c × x ≢ c') (d rₐ rₓ pk c c')

R : ★
R = Rₐ × Rₐ' × Rₖ × Rₑ × Rₑ

Game : ★
Game = Adv → R → Bit

⅁ : Bit → Game
⅁ b (m , d) (rₐ , rₐ' , rₖ , rₑ₀ , rₑ₁) with KeyGen rₖ
... | pk , sk = b′ where
  open Eval Dec sk
  
  ev = evalM (m rₐ pk)
  mb = proj (proj₁ ev)
  rₓ = proj₂ ev

  c₀  = Enc pk (mb b)       rₑ₀
  c₁  = Enc pk (mb (not b)) rₑ₁
  b′ = evalC (d rₐ' rₓ pk c₀ c₁)

