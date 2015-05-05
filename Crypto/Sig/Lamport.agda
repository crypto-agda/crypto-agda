{-# OPTIONS --without-K #-}
open import Function using (_∘_)
open import Data.Nat.NP hiding (_==_)
open import Data.Product.NP renaming (map to ×-map)
open import Data.Bit hiding (_==_)
open import Data.Bits
open import Data.Bits.Properties
open import Data.Vec.NP
open import Relation.Binary.PropositionalEquality.NP
import Crypto.Sig.LamportOneBit

module Crypto.Sig.Lamport
          (#digest  : ℕ)
          (#seed    : ℕ)
          (#secret  : ℕ)
          (#message : ℕ)
          (hash-secret    : Bits #secret → Bits #digest)
          (seed-expansion : Bits #seed   → Bits (#message * 2* #secret))
          where

module OTS1 = Crypto.Sig.LamportOneBit #secret #digest hash-secret

H  = hash-secret
H² = map2* #secret #digest H

#signkey1   = OTS1.#signkey
#verifkey1  = OTS1.#verifkey
#signature1 = OTS1.#signature
#signkey    = #message * #signkey1
#verifkey   = #message * #verifkey1
#signature  = #message * #signature1

Digest     = Bits #digest
Seed       = Bits #seed
Secret     = Bits #secret
SignKey    = Bits #signkey
Message    = Bits #message
Signature  = Bits #signature
VerifKey   = Bits #verifkey

verif-key : SignKey → VerifKey
verif-key = map* #message OTS1.verif-key

module verifkey (vk : VerifKey) where
  vk1s = group #message #verifkey1 vk

  concat-vk1s : concat vk1s ≡ vk
  concat-vk1s = concat-group #message #verifkey1 vk

module signkey (sk : SignKey) where
  sk1s = group #message #signkey1 sk
  sc1s = map OTS1.signkey.skP sk1s
  vk   = verif-key sk
  open verifkey vk public
  sc1s-sk1s : map (uncurry _++_) sc1s ≡ sk1s
  sc1s-sk1s = ! map-∘ (uncurry _++_) OTS1.signkey.skP sk1s
            ∙ map-id= (take-drop-lem #secret) sk1s
  H-sc1s-sk1s : map (uncurry _++_ ∘ ×-map H H) sc1s ≡ map H² sk1s
  H-sc1s-sk1s = ! map-∘= (map2*-++ H) sc1s ∙ ap (map H²) sc1s-sk1s

module signature (sig : Signature) where
  sig1s = group #message #signature1 sig

  concat-sig1s : concat sig1s ≡ sig
  concat-sig1s = concat-group #message #secret sig

key-gen : Seed → VerifKey × SignKey
key-gen s = vk , sk
  module key-gen where
    sk = seed-expansion s
    vk = verif-key sk

sign : SignKey → Message → Signature
sign sk m = sig
  module sign where
    open signkey sk public
    sig1s = map OTS1.sign sk1s ⊛ m
    sig   = concat sig1s

    group-sig : group #message #signature1 sig ≡ sig1s
    group-sig = group-concat sig1s

verify : VerifKey → Message → Signature → Bit
verify vk m sig = and checks
  module verify where
    open verifkey  vk  public
    open signature sig public
    checks = map OTS1.verify vk1s ⊛ m ⊛ sig1s

private
  module lemma {#m} (sk : Bits (suc #m * #signkey1))
                    (b : Bit) (m : Bits #m) where
    skL  = take #signkey1 sk
    skH  = drop #signkey1 sk
    vkL  = OTS1.verif-key skL
    vkH  = map* #m OTS1.verif-key skH
    sigL = OTS1.sign skL b
    sigH = concat (map OTS1.sign (group #m #signkey1 skH) ⊛ m)

verifkey-is-hash-sig : ∀ sk m (open signkey sk)
                       → map (take2* _) m ⊛ vk1s
                       ≡ map H (map OTS1.sign sk1s ⊛ m)
verifkey-is-hash-sig sk m = lemma sk m
  module verifkey-is-hash-sig where
    lemma : ∀ {#m} sk m → map (take2* _) m ⊛ group #m #verifkey1 (map* #m OTS1.verif-key sk)
                        ≡ map hash-secret (map OTS1.sign (group #m #signkey1 sk) ⊛ m)
    lemma sk [] = refl
    lemma {suc #m} sk (b ∷ m)
      rewrite (let open lemma sk b m in take-++ #verifkey1 vkL vkH)
            | (let open lemma sk b m in drop-++ #verifkey1 vkL vkH)
            | (let open lemma sk b m in take-++ #signkey1 skL skH)
            | (let open lemma sk b m in drop-++ #signkey1 skL skH)
            | (let open lemma sk b m in lemma skH m)
            | (let open lemma sk b m in OTS1.verifkey-is-hash-sig skL b)
      = refl

verify-correct-sig : ∀ sk m → verify (verif-key sk) m (sign sk m) ≡ 1b
verify-correct-sig sk m = lemma sk m
  module verify-correct-sig where
    lemma : ∀ {#m} sk m → and (map OTS1.verify (group #m #verifkey1 (map* #m OTS1.verif-key sk)) ⊛ m ⊛ group #m #signature1
                              (concat (map OTS1.sign (group #m #signkey1 sk) ⊛ m))) ≡ 1b
    lemma sk [] = refl
    lemma sk (b ∷ m)
      rewrite (let open lemma sk b m in take-++ #verifkey1 vkL vkH)
            | (let open lemma sk b m in drop-++ #verifkey1 vkL vkH)
            | (let open lemma sk b m in take-++ #signature1 sigL sigH)
            | (let open lemma sk b m in drop-++ #signature1 sigL sigH)
            | (let open lemma sk b m in OTS1.verify-correct-sig skL b)
            | (let open lemma sk b m in lemma skH m)
            = refl
-- -}
-- -}
-- -}
-- -}
