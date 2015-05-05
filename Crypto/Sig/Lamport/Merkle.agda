{-# OPTIONS --without-K #-}
open import Function using (id; _∘_; _$_; flip)
open import Data.Nat.NP hiding (_==_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product.NP renaming (map to ×-map)
open import Data.Bit hiding (_==_)
open import Data.Bits
open import Data.Bits.Properties
open import Data.Vec.NP
open import Relation.Binary.PropositionalEquality.NP
open ≡-Reasoning
import Crypto.Sig.Lamport

module Crypto.Sig.Lamport.Merkle
          (#digest   : ℕ)
          (#seed     : ℕ)
          (#secret   : ℕ)
          (#message  : ℕ)
          (hash-secret    : Bits #secret → Bits #digest)
          (hash-node      : Bits (2* #digest) → Bits #digest)
          (hash-verif-key : Bits (#message * 2* #digest) → Bits #digest)
          (seed-expansion : Bits #seed   → Bits (#message * 2* #secret))
          where

module B = Crypto.Sig.Lamport #digest #seed #secret #message hash-secret seed-expansion
module B1 = B.OTS1

open B using (H²)

H = hash-secret

#signkey   = B.#signkey
#verifkey  = #digest
#signature = B.#signature + #message * #digest

Digest     = Bits #digest
Seed       = Bits #seed
Secret     = Bits #secret
SignKey    = Bits #signkey
Message    = Bits #message
Signature  = Bits #signature
VerifKey   = Bits #verifkey

module signature (sig : Signature) where
  sigB        = take B.#signature sig
  module sigB = B.signature sigB
  sigB1s      = sigB.sig1s
  sigL1s      = map H sigB1s
  sigH        = drop B.#signature sig
  sigH1s      = group #message #digest sigH

verif-key : SignKey → VerifKey
verif-key = hash-verif-key
          ∘ B.verif-key

module signkey (sk : SignKey) where
  open B.signkey sk public renaming (vk to vkF) -- F"ull"
  vk   = verif-key sk

key-gen : Seed → VerifKey × SignKey
key-gen s = vk , sk
  module key-gen where
    sk = seed-expansion s
    vk = verif-key sk

co-sign : Bits (2* #secret) → Bit → Digest
co-sign s b = H (B1.sign s (not b))

sign : SignKey → Message → Signature
sign sk m = sig
  module sign where
    open signkey sk public
    sigL   = B.sign sk m
    sigH1s = map co-sign sk1s ⊛ m
    sigB1s = map B1.sign sk1s ⊛ m
    sigL1s = map H sigB1s
    sigH   = concat sigH1s
    sig    = sigL ++ sigH
    module sigL = B.sign sk m
    module sig  = signature sig
    sigH1s-spec : sig.sigH1s ≡ sigH1s
    sigH1s-spec = sig.sigH1s                  ≡⟨ ap (group #message #digest) (drop-++ B.#signature sigL sigH) ⟩
                  group #message #digest sigH ≡⟨ group-concat sigH1s ⟩
                  sigH1s                      ∎
    sigB1s-spec : sig.sigB1s ≡ sigB1s
    sigB1s-spec = sig.sigB1s                  ≡⟨ ap (group #message #secret) (take-++ B.#signature sigL sigH) ⟩
                  group #message #secret sigL ≡⟨ group-concat sigL.sig1s ⟩
                  sigB1s                      ∎
    sigL1s-spec : sig.sigL1s ≡ sigL1s
    sigL1s-spec = ap (map H) sigB1s-spec

twist-, : Bit → Digest → Digest → Digest × Digest
twist-, b sL sH = proj′ (sL , sH) b , proj′ (sH , sL) b

twist-++ : ∀ {n}(b : Bit)(sL sH : Bits n) → Bits (2* n)
twist-++ b sL sH = proj′ (sL , sH) b ++ proj′ (sH , sL) b

twist-++-map2* : ∀ {m n}(f : Bits m → Bits n) b sL sH
               → map2* m n f (twist-++ b sL sH) ≡ twist-++ b (f sL) (f sH)
twist-++-map2* f 0b sL sH rewrite take-++ _ sL sH | drop-++ _ sL sH = refl
twist-++-map2* f 1b sL sH rewrite take-++ _ sH sL | drop-++ _ sH sL = refl

twist-++-not : ∀ {n}(f : Bit → Bits n) b
               → twist-++ b (f b) (f (not b)) ≡ f 0b ++ f 1b
twist-++-not f 0b = refl
twist-++-not f 1b = refl

verify : VerifKey → Message → Signature → Bit
verify vk m sig = root-hash == vk
  module verify where
    open signature sig public
    sig1s     = map twist-++ m ⊛ sigL1s ⊛ sigH1s
    root-hash = hash-verif-key (concat sig1s)

lemma1 : ∀ sk b → twist-++ b (H (B1.sign sk b)) (H (B1.sign sk (not b))) ≡ H² sk
lemma1 sk b =
  twist-++ b (H (B1.sign sk b)) (H (B1.sign sk (not b)))
      ≡⟨ ! twist-++-map2* H b _ _ ⟩
  H² (twist-++ b (B1.sign sk b) (B1.sign sk (not b)))
      ≡⟨ ap H² (twist-++-not (B1.sign sk) b) ⟩
  H² (B1.sign sk 0b ++ B1.sign sk 1b)
      ≡⟨ ap H² (B1.sign-both-reveals-signkey sk) ⟩
  H² sk
      ∎

verify-correct-sig : ∀ sk m → verify (verif-key sk) m (sign sk m) ≡ 1b
verify-correct-sig sk m = ==-reflexive {xs = root-hash} lemma
  where
     vk = verif-key sk
     sig = sign sk m
     module sig = sign sk m
     module sk = signkey sk
     open verify vk m sig

     lemma-pointwise : ∀ (i : Fin #message) →
           (map twist-++ m ⊛ sig.sigL1s ⊛ sig.sigH1s ‼ i) ≡ 
           (map H² sig.sk1s ‼ i)
     lemma-pointwise i =
       (map twist-++ m ⊛ sig.sigL1s ⊛ sig.sigH1s ‼ i)
           -- Pushes the lookup down the operations map/⊛
           ≡⟨ ‼-⊛= i {map twist-++ m ⊛ sig.sigL1s}
                (‼-⊛= i {map twist-++ m}
                   (‼-map= i twist-++ refl)
                   (‼-map= i H (‼-⊛= i (‼-map i _ _) refl)))
                (‼-⊛= i (‼-map i co-sign sig.sk1s) refl) ⟩
       twist-++ (m ‼ i) (H (B1.sign (sig.sk1s ‼ i) (m ‼ i))) (H (B1.sign (sig.sk1s ‼ i) (not (m ‼ i))))
           ≡⟨ lemma1 (sig.sk1s ‼ i) (m ‼ i) ⟩
       H² (sig.sk1s ‼ i)
           -- Wrap-up the lookup through the map
           ≡⟨ ! ‼-map i H² _ ⟩
       (map H² sig.sk1s ‼ i)
           ∎

     lemma : root-hash ≡ vk
     lemma = ap (hash-verif-key ∘ concat)
                (map twist-++ m ⊛ sigL1s ⊛ sigH1s
                   -- Since the signature to be verified is known to come from
                   -- the sign function, one can symbolically reduce the
                   -- processing of the bit vector layout done on both parts of
                   -- the signature (only take/drop-++, group-concat).
                   ≡⟨ ap₂ _⊛_ (ap₂ _⊛_ refl sig.sigL1s-spec) sig.sigH1s-spec ⟩
                 map twist-++ m ⊛ sig.sigL1s ⊛ sig.sigH1s
                   -- One proves this equality pointwise for all index in the
                   -- message m.
                   ≡⟨ vec= lemma-pointwise ⟩
                 map B1.verif-key sk.sk1s ∎)
-- -}
-- -}
-- -}
-- -}
