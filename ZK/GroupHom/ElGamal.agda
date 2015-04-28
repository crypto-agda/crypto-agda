{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Function using (flip; _∘_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Two
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP using (_≡_; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import Algebra.Group
open import Algebra.Group.Constructions
open import Algebra.Group.Homomorphism
import ZK.SigmaProtocol.KnownStatement
import ZK.GroupHom
open import ZK.GroupHom.Types

module ZK.GroupHom.ElGamal
  (G+ G* : Type)
  (𝔾+ : Group G+)
  (𝔾* : Group G*)
  (_==_ : G* → G* → 𝟚)
  (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
  (==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y)
  (_^_ : G* → G+ → G*)
  (^-hom : ∀ b → GroupHomomorphism 𝔾+ 𝔾* (_^_ b))
  (g : G*)
  where

  open Additive-Group 𝔾+
  open Multiplicative-Group 𝔾* hiding (_^_)

-- TODO: Re-use another module
  module ElGamal-encryption where
    record CipherText : Type where
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
    dec x ct = (α ^ x)⁻¹ * β where
      open CipherText ct

  open ElGamal-encryption

  -- CP : (g₀ g₁ u₀ u₁ : G) (w : ℤq) → Type
  -- CP g₀ g₁ u₀ u₁ w = (g₀ ^ w ≡ u₀) × (g₁ ^ w ≡ u₁)

  -- CP : (g₀ g₁ u₀ u₁ : G*) (w : G+) → Type
  -- CP g₀ g₁ u₀ u₁ w = ✓ (((g₀ ^ w) == u₀) ∧ ((g₁ ^ w) == u₁))

  module _ (y  : PubKey)
           (M  : Message)
           (ct : CipherText)
           where
    module CT = CipherText ct

    KnownEncRnd : EncRnd → Type
    KnownEncRnd r = enc y r M ≡ ct

    known-enc-rnd : GrpHom _ _ KnownEncRnd
    known-enc-rnd = record
      { 𝔾+ = 𝔾+
      ; 𝔾* = Product.×-grp 𝔾* 𝔾*
      ; _==_ = λ x y → fst x == fst y ∧ snd x == snd y
      ; ✓-== = λ e → ✓∧ (✓-== (ap fst e)) (✓-== (ap snd e))
      ; ==-✓ = λ e → let p = ✓∧× e in
                     ap₂ _,_ (==-✓ (fst p))
                             (==-✓ (snd p))
      ; φ = _
      ; φ-hom = Pair.pair-hom _ _ _ (_^_ g) (^-hom g)
                                    (_^_ y) (^-hom y)
      ; y = CT.α , CT.β / M
      ; φ⇒P = λ _ e → ap₂ (λ p q → fst p , q) e
                          (ap (flip _*_ M ∘ snd) e ∙ ! /-*)
      ; P⇒φ = λ _ e → ap₂ _,_ (ap CipherText.α e)
                              (*-/ ∙ ap (flip _/_ M) (ap CipherText.β e))
      }

    KnownDec : PrivKey → Type
    KnownDec x = (g ^ x ≡ y) × (dec x ct ≡ M)

    open ≡-Reasoning

    /⁻¹-* : ∀ {x y} → (x / y)⁻¹ * x ≡ y
    /⁻¹-* {x} {y} =
      (x / y)⁻¹ * x        ≡⟨ ap (λ z → z * x) ⁻¹-hom′ ⟩
      y ⁻¹ ⁻¹ * x ⁻¹ * x   ≡⟨ *-assoc ⟩
      y ⁻¹ ⁻¹ * (x ⁻¹ * x) ≡⟨ ap₂ _*_ ⁻¹-involutive (fst ⁻¹-inverse) ⟩
      y * 1#               ≡⟨ *1-identity ⟩
      y                    ∎

    /-⁻¹* : ∀ {x y} → x / (y ⁻¹ * x) ≡ y
    /-⁻¹* {x} {y} =
      x * (y ⁻¹ * x) ⁻¹    ≡⟨ ap (_*_ x) ⁻¹-hom′ ⟩
      x * (x ⁻¹ * y ⁻¹ ⁻¹) ≡⟨ ! *-assoc ⟩
      (x * x ⁻¹) * y ⁻¹ ⁻¹ ≡⟨ *= (snd ⁻¹-inverse) ⁻¹-involutive ⟩
      1# * y               ≡⟨ 1*-identity ⟩
      y                    ∎

    known-dec : GrpHom _ _ KnownDec
    known-dec = record
      { 𝔾+ = 𝔾+
      ; 𝔾* = Product.×-grp 𝔾* 𝔾*
      ; _==_ = λ x y → fst x == fst y ∧ snd x == snd y
      ; ✓-== = λ e → ✓∧ (✓-== (ap fst e)) (✓-== (ap snd e))
      ; ==-✓ = λ e → let p = ✓∧× e in
                     ap₂ _,_ (==-✓ (fst p))
                             (==-✓ (snd p))
      ; φ = _
      ; φ-hom = Pair.pair-hom _ _ _ (_^_ g)    (^-hom g)
                                    (_^_ CT.α) (^-hom CT.α)
      ; y = y , CT.β / M
      ; φ⇒P = λ x e → ap fst e , ap (λ z → z ⁻¹ * CT.β) (ap snd e) ∙ /⁻¹-*
      ; P⇒φ = λ x e → ap₂ _,_ (fst e) (! /-⁻¹* ∙ ap (_/_ CT.β) (snd e))
      }

-- -}
-- -}
-- -}
