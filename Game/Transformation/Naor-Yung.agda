{-# OPTIONS --without-K #-}
open import Type
open import Data.Two
open import Data.Maybe
open import Data.Product.NP
open import Relation.Binary.PropositionalEquality

open import Crypto.Schemes

module Game.Transformation.Naor-Yung
  (pke : Pubkey-encryption)
  (pok : PoK-message-equality-enc pke)
  where

open Pubkey-encryption pke
open PoK-message-equality-enc pok

PubKey' = PubKey ²
SecKey' = SecKey
Message' = Message
CipherText' = CipherText ² × Proof

Rₑ' = Rₑ ²
Rₖ' = Rₖ × Rₖ

key-gen' : Rₖ' → PubKey' × SecKey'
key-gen' (ra , rb) = let (pa , sa) = key-gen ra
                         (pb , sb) = key-gen rb
                     in proj (pa , pb) , sa

enc' : PubKey' → Message' → Rₑ' → CipherText'
enc' pp m rₑ = let c_ = λ b → enc (pp b) m (rₑ b)
                      in c_ , prove m pp rₑ c_

dec' : SecKey' → CipherText' → Maybe Message'
dec' sa (cc , pi) = [0: nothing 1: dec sa (cc 0₂) ]′ (verify cc pi)

functionally-correct' :
    ∀ rₖ rₑ m → let (pk , sk) = key-gen' rₖ in
                dec' sk (enc' pk m rₑ) ≡ just m
functionally-correct' rₖ rₑ m
  rewrite functionally-correct (fst rₖ) (rₑ 0₂) m
        | functionally-correct (snd rₖ) (rₑ 1₂) m
        | correct-pok m (fst (key-gen' rₖ)) rₑ = refl

NY-encryption : Pubkey-encryption
NY-encryption = record
                  { pko = record
                    { key-gen = key-gen'
                    ; enc = enc'
                    ; dec = dec'
                    }
                  ; functionally-correct = functionally-correct'
                  }
-- -}
-- -}
-- -}
-- -}
