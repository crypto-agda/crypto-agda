open import Type using (Type)
open import Function using (flip)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum.NP
open import Data.Bool.Base using (Bool) renaming (T to ✓)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; _≢_; idp; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import Algebra.Group
open import ZK.Types using (Cyclic-group; module Cyclic-group
                           ; Cyclic-group-properties; module Cyclic-group-properties)
import ZK.SigmaProtocol.KnownStatement


module ZK.GroupHom where
postulate
  G+ G* : Type
  -- grp-G+-comm : Abelian-Group G+
  grp-G+ : Group G+
  -- grp-G* : Group G*
  grp-G*-comm : Abelian-Group G*
module _
--     {G+ G* : Type} (grp-G+ : Group G+) (grp-G* : Group G*)

    {C : Type} -- ℤ
    (φ : G+ → G*) -- For instance φ(x) = g^x
    (y : G*)
    (_==_ : G* → G* → Bool)
    (_^_ : G* → C → G*)
    (_⊗_ : G+ → C → G+)

    (_−ᶜ_ : C → C → C)
    {-
    -- Coprime m n ↔ GCD m n 1
    (Coprime : (m n : C) → Type)
    (_<_ : C → C → Type)
    (≢-< : ∀ {c₀ c₁} → c₀ ≢ c₁ → (c₀ < c₁) ⊎ (c₁ < c₀))

    (ℓ : C)
    (u : G+)(φu : φ u ≡ y ^ ℓ)
    (<-coprime : ∀ {c₀ c₁} → c₁ < c₀ → Coprime (c₀ −ᶜ c₁) ℓ)
    (egcd : (m n : C) → C × C)
    -- (egcd-coprime : ∀ m n → let a , b = egcd m n in {!!})
    -}
    (modinv : C → C)
    where

  -- grp-G+ = Abelian-Group.grp grp-G+-comm
  -- open Additive-Abelian-Group grp-G+-comm
  open Additive-Group grp-G+
  grp-G* = Abelian-Group.grp grp-G*-comm
  -- open Multiplicative-Group grp-G*
  open Multiplicative-Abelian-Group grp-G*-comm

  Commitment = G*
  Challenge  = C
  Response   = G+
  Witness    = G+
  Randomness = G+
  _∈y : Witness → Type
  x ∈y = φ x ≡ y

  open ZK.SigmaProtocol.KnownStatement Commitment Challenge Response Randomness Witness _∈y public

  prover : Prover
  prover a x = (φ a) , response
     where response : Challenge → Response
           response c = (a + (x ⊗ c))

  verifier : Verifier
  verifier (mk A c s) = (φ s) == (A * (y ^ c))

  Schnorr : Σ-Protocol
  Schnorr = (prover , verifier)

  -- The simulator shows why it is so important for the
  -- challenge to be picked once the commitment is known.
  -- To fake a transcript, the challenge and response can
  -- be arbitrarily chosen. However to be indistinguishable
  -- from a valid proof they need to be picked at random.
  simulator : Simulator
  simulator c s = A
      where
        -- Compute A, such that the verifier accepts!
        A = (φ s) / (y ^ c)

  -- The extractor shows the importance of never reusing a
  -- commitment. If the prover answers to two different challenges
  -- comming from the same commitment then the knowledge of the
  -- prover (the witness) can be extracted.
  extractor : Extractor verifier
  extractor t² = x'
      module Witness-extractor where
        open Transcript² t²
        rd = get-f₀ − get-f₁
        cd = get-c₀ −ᶜ get-c₁
        {-
        ab = egcd cd ℓ
        a = fst ab
        b = snd ab
        x' = u ⊗ a + rd ⊗ b
        -}
        x' = rd ⊗ modinv cd
  
  module Proofs
    (φ-hom : GroupHomomorphism grp-G+ grp-G* φ)
    (✓-== : ∀ {x y} → x ≡ y → ✓ (x == y))
    (==-✓ : ∀ {x y} → ✓ (x == y) → x ≡ y)
    (φ⁻¹ : G* → G+)
    .(φ∘φ⁻¹ : ∀ y → φ (φ⁻¹ y) ≡ y)
    (φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y)
    (φ-hom-iterated : ∀ {x c} → φ (x ⊗ c) ≡ φ x ^ c)
    (^--  : ∀ {b x y} → b ^(x −ᶜ y) ≡ (b ^ x) / (b ^ y))
    (left-*-to-right-/ : ∀ {x y c} → x ⊗ c ≡ y → x ≡ y ⊗ modinv c)
     where
    open ≡-Reasoning
    open GroupHomomorphismProp grp-G+ grp-G* {φ} φ-hom

    correct : Correct Schnorr
    correct x a c w
      = ✓-== (φ(a + (x ⊗ c))
           ≡⟨ φ-hom ⟩
              A * (φ(x ⊗ c))
           ≡⟨ ap (λ z → A * z) φ-hom-iterated ⟩
              A * ((φ x) ^ c)
           ≡⟨ ap (λ z → A * (z ^ c)) w ⟩
              A * (y ^ c)
           ∎)
      where
        A = φ a

    shvzk : Special-Honest-Verifier-Zero-Knowledge Schnorr
    shvzk = record { simulator = simulator
                   ; correct-simulator = λ _ _ → ✓-== /-* }

    module _ (t² : Transcript² verifier) where
      private
        x = φ⁻¹ y

      open Transcript² t² renaming (get-A to A; get-c₀ to c₀; get-c₁ to c₁
                                   ;get-f₀ to f₀; get-f₁ to f₁)
      open Witness-extractor t²

      .φxcd≡φrd : _
      φxcd≡φrd = φ(x ⊗ cd)
                 ≡⟨ φ-hom-iterated ⟩
                   (φ x) ^ (c₀ −ᶜ c₁)
                 ≡⟨ ap₂ _^_ (φ∘φ⁻¹ y) idp ⟩
                   y ^ (c₀ −ᶜ c₁)
                 ≡⟨ ^-- ⟩
                   (y ^ c₀) / (y ^ c₁)
                 ≡⟨ ! cancels-/ ⟩
                   (A * (y ^ c₀)) / (A * (y ^ c₁))
                 ≡⟨ /= (! ==-✓ verify₀) (! ==-✓ verify₁) ⟩
                   (φ f₀) / (φ f₁)
                 ≡⟨ ! f-−-/ ⟩
                   φ rd
                 ∎

      .xcd≡rd : _
      xcd≡rd = φ-inj φxcd≡φrd

      -- The extracted x is correct
      .extractor-ok : φ x' ≡ y 
      extractor-ok = ! ap φ (left-*-to-right-/ xcd≡rd) ∙ φ∘φ⁻¹ y

    special-soundness : Special-Soundness Schnorr
    special-soundness = record { extractor = extractor
                               ; extract-valid-witness = extractor-ok }

    special-Σ-protocol : Special-Σ-Protocol
    special-Σ-protocol = record { Σ-protocol = Schnorr ; correct = correct ; shvzk = shvzk ; ssound = special-soundness }
-- -}
-- -}
-- -}
-- -}
