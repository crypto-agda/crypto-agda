{-# OPTIONS --without-K #-}
open import Type using (Type)
open import Type.Eq using (Eq?; _==_; ≡⇒==; ==⇒≡)
open import Function using (case_of_)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Binary.PropositionalEquality.Base using (_≡_; _≢_; idp; ap; ap₂; !_; _∙_; module ≡-Reasoning)
open import Algebra.Group
open import Algebra.Group.Homomorphism
import ZK.SigmaProtocol.KnownStatement

module ZK.GroupHom
    {G+ G* : Type} (grp-G+ : Group G+) (grp-G* : Group G*)
    {{eq?-G* : Eq? G*}}

    (open Additive-Group grp-G+ hiding (_⊗_))
    (open Multiplicative-Group grp-G* hiding (_^_))

    {C : Type} -- e.g. C ⊆ ℕ
    (_>_ : C → C → Type)
    (swap? : {c₀ c₁ : C} → c₀ ≢ c₁ → (c₀ > c₁) ⊎ (c₁ > c₀))
    (_⊗_ : G+ → C → G+)
    (_^_ : G* → C → G*)
    (_−ᶜ_ : C → C → C)
    (1/ : C → C)

    (φ : G+ → G*) -- For instance φ(x) = g^x
    (φ-hom : GroupHomomorphism grp-G+ grp-G* φ)
    (φ-hom-iterated : ∀ {x c} → φ (x ⊗ c) ≡ φ x ^ c)

    (Y : G*)

    (^-−ᶜ  : ∀ {c₀ c₁}(c> : c₀ > c₁) → Y ^(c₀ −ᶜ c₁) ≡ (Y ^ c₀) / (Y ^ c₁))
    (^-^-1/ : ∀ {c₀ c₁}(c> : c₀ > c₁) → (Y ^(c₀ −ᶜ c₁))^(1/(c₀ −ᶜ c₁)) ≡ Y)
    where

  Commitment = G*
  Challenge  = C
  Response   = G+
  Witness    = G+
  Randomness = G+
  _∈y : Witness → Type
  x ∈y = φ x ≡ Y

  open ZK.SigmaProtocol.KnownStatement Commitment Challenge Response Randomness Witness _∈y public

  prover : Prover
  prover a x = φ a , response
     where response : Challenge → Response
           response c = (x ⊗ c) + a

  verifier' : (A : Commitment)(c : Challenge)(s : Response) → _
  verifier' A c s = φ s == ((Y ^ c) * A)

  verifier : Verifier
  verifier (mk A c s) = verifier' A c s

  -- We still call it Schnorr since essentially not much changed.
  -- The scheme abstracts away g^ as an homomorphism called φ
  -- and one get to distinguish between the types C vs G+ and
  -- their operations _⊗_ vs _*_.
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
        A = (Y ^ c)⁻¹ * φ s

  swap-t²? : Transcript²[ _≢_ ] verifier → Transcript²[ _>_ ] verifier
  swap-t²? t² = t²'
      module Swap? where
        open Transcript² t² public
          using (verify₀; verify₁; c₀≢c₁)
          renaming ( get-A to A
                   ; get-f₀ to r₀; get-f₁ to r₁
                   ; get-c₀ to c₀; get-c₁ to c₁
                   )
        t²' = case swap? c₀≢c₁ of λ
              { (inl c₀>c₁) → mk A c₀ c₁ c₀>c₁ r₀ r₁ verify₀ verify₁
              ; (inr c₀<c₁) → mk A c₁ c₀ c₀<c₁ r₁ r₀ verify₁ verify₀
              }

  -- The extractor shows the importance of never reusing a
  -- commitment. If the prover answers to two different challenges
  -- comming from the same commitment then the knowledge of the
  -- prover (the witness) can be extracted.
  extractor : Extractor verifier
  extractor t² = x'
      module Witness-extractor where
        open Transcript² (swap-t²? t²) public
          using (verify₀; verify₁)
          renaming ( get-A to A
                   ; get-f₀ to r₀; get-f₁ to r₁
                   ; get-c₀ to c₀; get-c₁ to c₁
                   ; c₀≢c₁ to c₀>c₁
                   )
        rd   = r₀ − r₁
        cd   = c₀ −ᶜ c₁
        1/cd = 1/ cd
        x'   = rd ⊗ 1/cd

  open ≡-Reasoning
  open GroupHomomorphism φ-hom

  correct : Correct Schnorr
  correct x a c w
    = ≡⇒== (φ((x ⊗ c) + a)  ≡⟨ hom ⟩
            φ(x ⊗ c)  * A   ≡⟨ *= φ-hom-iterated idp ⟩
            (φ x ^ c) * A   ≡⟨ ap (λ z → (z ^ c) * A) w ⟩
            (Y ^ c)   * A   ∎)
    where
      A = φ a

  shvzk : Special-Honest-Verifier-Zero-Knowledge Schnorr
  shvzk = record { simulator = simulator
                 ; correct-simulator =
                    λ _ _ → ≡⇒== (! elim-*-!assoc= (snd ⁻¹-inverse)) }

  module _ (t² : Transcript² verifier) where
    open Witness-extractor t²

    φrd≡ycd : _
    φrd≡ycd
      = φ rd                        ≡⟨by-definition⟩
        φ (r₀ − r₁)                 ≡⟨ −-/ ⟩
        φ r₀ / φ r₁                 ≡⟨ /= (==⇒≡ verify₀) (==⇒≡ verify₁) ⟩
        (Y ^ c₀ * A) / (Y ^ c₁ * A) ≡⟨ elim-*-right-/ ⟩
        Y ^ c₀ / Y ^ c₁             ≡⟨ ! ^-−ᶜ c₀>c₁ ⟩
        Y ^(c₀ −ᶜ c₁)               ≡⟨by-definition⟩
        Y ^ cd                      ∎

    -- The extracted x is correct
    extractor-ok : φ x' ≡ Y
    extractor-ok
      = φ(rd ⊗ 1/cd)    ≡⟨ φ-hom-iterated ⟩
        φ rd ^ 1/cd     ≡⟨ ap₂ _^_ φrd≡ycd idp ⟩
        (Y ^ cd)^ 1/cd  ≡⟨ ^-^-1/ c₀>c₁ ⟩
        Y               ∎

  special-soundness : Special-Soundness Schnorr
  special-soundness = record { extractor = extractor
                             ; extract-valid-witness = extractor-ok }

  special-Σ-protocol : Special-Σ-Protocol
  special-Σ-protocol = record { Σ-protocol = Schnorr ; correct = correct ; shvzk = shvzk ; ssound = special-soundness }
-- -}
-- -}
-- -}
-- -}
