{-# OPTIONS --without-K #-}
open import Type using (Type; ★)
open import Function using (flip)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum.NP
open import Data.Zero
open import Data.Fin.NP using (Fin▹ℕ)
open import Data.Bool.Base using (Bool; _∧_) renaming (T to ✓)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP using (_≡_; _≢_; idp; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import Algebra.Group
open import Algebra.Group.Homomorphism
open import Data.Nat.NP hiding (_==_; _^_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties
open import Data.Nat.Primality
open import Data.Nat.DivMod.NP
import Data.Nat.ModInv
import ZK.SigmaProtocol.KnownStatement
import ZK.GroupHom
import ZK.GroupHom.NatChal as GH

module ZK.GroupHom.ElGamal
  (G+ G* : Type)
  (𝔾+ : Group G+)
  (𝔾* : Group G*)
  (_==_ : G* → G* → Bool)
  (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
  (==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y)
  (_^_ : G* → G+ → G*)
  (^-hom : ∀ b → GroupHomomorphism 𝔾+ 𝔾* (_^_ b))
  (g : G*)

  (q : ℕ)
  (q-prime : Prime q)

  (open Multiplicative-Group 𝔾* hiding (_^_))

  -- Can be turned into a dynamic test!
  --(G*-order : Y ^⁺ q ≡ 1#)

  (open Data.Nat.ModInv q q-prime)
  (missing : (x : ℕ) → x ≢ 0 → (1/ x *ℕ x) modℕ q ≡ 1)
 
  where

  open Additive-Group 𝔾+
  --open Multiplicative-Group G* hiding (_^_)
  --module φ = GroupHomomorphism φ-hom
  module 𝔾* = Group 𝔾*

-- TODO: Re-use another module
  module ElGamal-encryption where
    record CipherText : ★ where
      constructor _,_
      field
        α β : G*

    PubKey  = G*
    PrivKey = G+
    EncRnd  = G+ {- randomness used for encryption of ct -}
    Message = G* {- plain text message -}

    enc : PubKey → EncRnd → Message → CipherText
    enc y r M = α , β where
      α = g ^ r
      β = (y ^ r) * M

    dec : PrivKey → CipherText → Message
    dec x ct = β / (α ^ x) where
      open CipherText ct

  open ElGamal-encryption

  -- CP : (g₀ g₁ u₀ u₁ : G) (w : ℤq) → Type
  -- CP g₀ g₁ u₀ u₁ w = (g₀ ^ w ≡ u₀) × (g₁ ^ w ≡ u₁)

  CP : (g₀ g₁ u₀ u₁ : G*) (w : G+) → Type
  CP g₀ g₁ u₀ u₁ w = ✓ (((g₀ ^ w) == u₀) ∧ ((g₁ ^ w) == u₁))

  module _ (y  : PubKey)
           (M  : Message)
           (ct : CipherText)
           where
    module CT = CipherText ct

    KnownEncRnd : EncRnd → Type
    KnownEncRnd r = enc y r M ≡ ct

    module GenKnownEncRnd = GH G+ (G* × G*) {!!} {!!} {!!} {!!} {!!} {!(g ∷ y ∷ [])!} {!!} (CT.α , CT.β / M) q q-prime {!!} missing
{--
    mapEncRnd : W-Map GenKnownEncRnd.Valid KnownEncRnd
    mapEncRnd = record { →Witness = id ; ←Witness = id
                       ; →Valid = λ w₀? → let (p₀ , p₁₂) = ✓∧× w₀?
                                              (p₁ , p₂)  = ✓∧× p₁₂ in
                                          ap₂ _,_ (==-✓ p₀) (pf (==-✓ p₁))
                       ; ←Valid = λ w₁? → ✓∧ (✓-== (ap CipherText.α w₁?))
                                             (✓∧ (✓-== (pf! (ap CipherText.β w₁?))) _)
                       }
     where
      pf : ∀ {M yr β} → yr ≡ β / M → yr · M ≡ β
      pf {M} e = ap (flip _·_ M) e ∙ ! /-·

      pf! : ∀ {M yr β} → yr · M ≡ β → yr ≡ β / M
      pf! {M} e = ·-/ ∙ ap (flip _/_ M) e

    module σEncRndKnowledge = Apply-W-Map mapEncRnd (GenKnownEncRnd.Proofs.Σ-structure cg-props)

    KnownDec : PrivKey → Type
    KnownDec x = (g ^ x ≡ y) × (dec x ct ≡ M)

    module GenKnownDec = Generic (g ∷ CT.α ∷ []) (y ∷ (CT.β / M) ∷ [])

    mapDec : W-Map GenKnownDec.Valid KnownDec
    mapDec = record { →Witness = id ; ←Witness = id
                    ; →Valid = λ w₀? → let (p₀ , p₁₂) = ✓∧× w₀?
                                           (p₁ , p₂)  = ✓∧× p₁₂ in
                                       ==-✓ p₀ , pf (==-✓ p₁)
                    ; ←Valid = λ w₁? → ✓∧ (✓-== (fst w₁?))
                                          (✓∧ (✓-== (pf! (snd w₁?))) _)
                    }
     where
      pf : ∀ {w M} → CT.α ^ w ≡ CT.β / M → dec w ct ≡ M
      pf {w} {M} e = ap (_/_ CT.β) e ∙ ! /-/

      pf! : ∀ {w M} → dec w ct ≡ M → CT.α ^ w ≡ CT.β / M
      pf! {w} {M} e = /-/ ∙ ap (_/_ CT.β) e

    module σKnownDec = Apply-W-Map mapEncRnd (GenKnownEncRnd.Proofs.Σ-structure cg-props)

-- -}
-- -}
-- -}
