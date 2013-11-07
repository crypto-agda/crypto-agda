open import Type
open import Data.Bit
open import Data.Maybe
open import Data.Product

module Game.Transformation.Naor-Yung
  (PubKey    : ★)
  (SecKey    : ★)
  (Message   : ★)
  (CipherText : ★)
  (Proof      : ★)
  

  -- randomness supply for, encryption, key-generation, adversary, adversary state
  (Rₑ Rₖ  : ★)
  (KeyGen : Rₖ → PubKey × SecKey)
  (Enc    : PubKey → Message → Rₑ → CipherText)
  (Dec    : SecKey → CipherText → Message)
  (Prove  : Message → PubKey → PubKey → Rₑ → Rₑ → CipherText → CipherText → Proof)
  (Verify : (Bit → CipherText) → Proof → Bit)
where

PubKey' = Bit → PubKey
SecKey' = SecKey
Message' = Message
CipherText' = (Bit → CipherText) × Proof

Rₑ' = Rₑ × Rₑ
Rₖ' = Rₖ × Rₖ

KeyGen' : Rₖ' → PubKey' × SecKey'
KeyGen' (ra , rb) = let (pa , sa) = KeyGen ra
                        (pb , sb) = KeyGen rb
                     in proj (pa , pb) , sa

Enc' : PubKey' → Message' → Rₑ' → CipherText'
Enc' pp m (ra , rb) = let pa = pp 0b
                          pb = pp 1b
                          ca = Enc pa m ra
                          cb = Enc pb m rb
                       in proj′ (ca , cb) , Prove m pa pb ra rb ca cb

Dec' : SecKey' → CipherText' → Maybe Message'
Dec' sa (cc , pi) = [0: nothing 1: (just (Dec sa (cc 0b))) ]′ (Verify cc pi)
