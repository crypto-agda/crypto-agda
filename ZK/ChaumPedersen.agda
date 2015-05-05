{-# OPTIONS --without-K #-}
open import Type
open import Function
open import Data.Zero
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec renaming (map to _<$>_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) hiding (zip)
open import Data.Two.Base hiding (_==_)
open import Data.ShapePolymorphism
open import Relation.Binary.PropositionalEquality.NP
open import ZK.Types
open import ZK.Statement
open import ZK.SigmaProtocol.Signature
open import ZK.SigmaProtocol.Structure
open import ZK.SigmaProtocol.Map
import ZK.SigmaProtocol.KnownStatement as ΣProto
import ZK.SigmaProtocol.Types as ΣTypes
import ZK.Lemmas

module ZK.ChaumPedersen
    {G ℤq : ★}
    (cg : Cyclic-group G ℤq)
    where
  {-
  -- Hint: Postulates yield nicer goals than parameters
  postulate
    G ℤq : ★
    cg : Cyclic-group G ℤq
  -}
  open Cyclic-group cg hiding (suc)

  Challenge  = ℤq
  Response   = ℤq
  Randomness = ℤq
  Witness    = Randomness

  _‼_ : ∀ {n a}{A : Set a} → Vec A n → Fin n → A
  _‼_ = flip lookup

  and : ∀ {n} → Vec 𝟚 n → 𝟚
  and = foldr _ _∧_ 1₂

  {-
  ✓-and : ∀ {a}{A : Set a}
           (f : A → 𝟚)(✓f : (x : A) → ✓ (f x))
           {n}(xs : Vec A n)
         → ✓(and (f <$> xs))
  ✓-and = {!!}

  ✓-and : ∀ {a b}{A : Set a}{B : Set b}
            {f : A → B → 𝟚}
            (✓f : (x : A)(y : B) → ✓(f x y))
            {n}(xs : Vec A n)(ys : Vec B n)
         → ✓(and (f <$> xs ⊛ ys))
  ✓-and ✓f [] [] = _
  ✓-and {f = f} ✓f (x ∷ xs) (y ∷ ys) = ✓∧ (✓f x y) (✓-and ✓f xs ys)

  ‼-⊛ : ∀ {n a b}{A : Set a}{B : Set b}
          (fs : Vec (A → B) n)(xs : Vec A n)
          (l : Fin n) → (fs ⊛ xs)‼ l ≡ (fs ‼ l) (xs ‼ l)
  ‼-⊛ = {!!}
  -}

  ✓-and : ∀ {n}{xs : Vec 𝟚 n} → (∀ l → ✓(xs ‼ l)) → ✓(and xs) 
  ✓-and {xs = []}     p = _
  ✓-and {xs = x ∷ xs} p = ✓∧ (p zero) (✓-and (p ∘ suc))

  ✓-and' : ∀ {n}{xs : Vec 𝟚 n} → ✓(and xs) → ∀ l → ✓(xs ‼ l)
  ✓-and' {xs = x ∷ xs} e zero = ✓∧₁ {x} e
  ✓-and' {xs = x ∷ xs} e (suc l) = ✓-and' (✓∧₂ {x} e) l

  valid1 : (w : Witness) (y u : G) → 𝟚
  valid1 w y u = y ^ w == u

  verify1 : (c : Challenge)(s : Response)(y u A : G) → 𝟚
  verify1 c s y u A = y ^ s == A · (u ^ c)

  -- Compute each part of the commitment, such that the verifier accepts!
  simulator1 : (c : Challenge)(s : Response)(y u : G) → G
  simulator1 c s y u = (y ^ s) / (u ^ c)

  correct-simulator‼ : ∀ {n}(ys us : Vec G n) c s l →
         let simulator = simulator1 c s <$> ys ⊛ us in
         ✓((verify1 c s <$> ys ⊛ us ⊛ simulator) ‼ l)
  correct-simulator‼ (y ∷ ys) (u ∷ us) c s zero    = ≡⇒== /-·
  correct-simulator‼ (y ∷ ys) (u ∷ us) c s (suc l) = correct-simulator‼ ys us c s l

  module _ (c₀ c₁ f₀ f₁ : ℤq) where
    module Lemma = ZK.Lemmas cg c₀ c₁ f₀ f₁
    private
        fd = f₀ − f₁
        cd = c₀ − c₁
        w' = fd * cd ⁻¹
    .extractor-ok‼ : ∀ {n}(ys us : Vec G n)(As : Vec G n)
                      (l : Fin n)
                      (verify₀ : ✓((verify1 c₀ f₀ <$> ys ⊛ us ⊛ As)‼ l))
                      (verify₁ : ✓((verify1 c₁ f₁ <$> ys ⊛ us ⊛ As)‼ l))
                   → ✓((valid1 w' <$> ys ⊛ us) ‼ l)
    extractor-ok‼ (y ∷ ys) (u ∷ us) (A ∷ As) zero    v0 v1 = ≡⇒== (Lemma.proof A u y v0 v1)
    extractor-ok‼ (y ∷ ys) (u ∷ us) (A ∷ As) (suc l) v0 v1 = extractor-ok‼ ys us As l v0 v1

  module _ (x w c : ℤq) where
    private
      s = x + (w * c)

    module Correct1 (y u : G) (e : ✓(valid1 w y u)) where
        open ≡-Reasoning
        A = y ^ x
        pf₀ = y ^(x + w * c)
            ≡⟨ ^-+ ⟩
              A · (y ^(w * c))
            ≡⟨ ap (λ z → A · z) ^-* ⟩
              A · ((y ^ w) ^ c)
            ≡⟨ ap (λ z → A · (z ^ c)) (==⇒≡ e) ⟩
              A · (u ^ c)
            ∎
        pf : ✓(verify1 c s y u A)
        pf = ≡⇒== pf₀

    correct‼ : ∀ {n} (ys us : Vec G n) l
               (es : ✓ ((valid1 w <$> ys ⊛ us) ‼ l)) →
             let As = (λ y → y ^ x) <$> ys in
             ✓((verify1 c s <$> ys ⊛ us ⊛ As) ‼ l)
    correct‼ (y ∷ ys) (u ∷ us) zero    e = Correct1.pf y u e
    correct‼ (y ∷ ys) (u ∷ us) (suc l) e = correct‼ ys us l e

  module Generic {n} (ys us : Vec G n) where

    Commitment : ★
    Commitment = Vec G n

    Valid : Witness → Type
    Valid w = ✓ (and (valid1 w <$> ys ⊛ us))

    open ΣProto Commitment Challenge Response Randomness Witness Valid public

    prover : Prover
    prover x w = commitment ΣTypes., response
     module CPProver where
      commitment1 : (y : G) → G
      commitment1 y = y ^ x

      commitment : Commitment
      commitment = commitment1 <$> ys

      response : Challenge → Response
      response c = x + (w * c)

    verifier : Verifier
    verifier (mk As c s) = and (verify1 c s <$> ys ⊛ us ⊛ As)

    ChaumPedersen : Σ-Protocol
    ChaumPedersen = prover , verifier

    -- This simulator shows why it is so important for the
    -- challenge to be picked once the commitment is known.
    --
    -- To fake a transcript, the challenge and response can
    -- be arbitrarily chosen. However to be indistinguishable
    -- from a valid proof it they need to be picked at random.
    simulator : Simulator
    simulator c s = simulated-commitment
      module CPSimulator where

        simulated-commitment : Commitment
        simulated-commitment = simulator1 c s <$> ys ⊛ us

        simulated-transcript : Transcript
        simulated-transcript = ΣTypes.mk simulated-commitment c s

    -- The extractor shows the importance of never reusing a
    -- commitment. If the prover answers to two different challenges
    -- comming from the same commitment then the knowledge of the
    -- prover (the witness) can be extracted.
    extractor : Extractor verifier
    extractor t² = w'
        module Witness-extractor where
          open Transcript² t²
          fd = get-f₀ − get-f₁
          cd = get-c₀ − get-c₁
          w' = fd * cd ⁻¹

    open ≡-Reasoning

    correct-simulator : Correct-simulator verifier simulator
    correct-simulator c s = ✓-and (correct-simulator‼ ys us c s)

    shvzk : Special-Honest-Verifier-Zero-Knowledge ChaumPedersen
    shvzk = record { correct-simulator = correct-simulator }

    correct : Correct (prover , verifier)
    correct w x c es = ✓-and (λ l → correct‼ x w c ys us l (✓-and' es l))

    module _ (t² : Transcript² verifier) where
      open Transcript² t² renaming (get-A to As; get-c₀ to c₀; get-c₁ to c₁
                                   ;get-f₀ to f₀; get-f₁ to f₁)
      open Witness-extractor t²

      -- The extracted w' is correct
      .extractor-ok : Valid w'
      extractor-ok = ✓-and λ l → extractor-ok‼ c₀ c₁ f₀ f₁ ys us As l
                                    (✓-and' verify₀ l) (✓-and' verify₁ l)

    -- All of this should not be in proofs...
    special-soundness : Special-Soundness ChaumPedersen
    special-soundness = record { extract-valid-witness = extractor-ok }

    special-Σ-protocol : Special-Σ-Protocol
    special-Σ-protocol = record { correct = correct ; shvzk = shvzk ; ssound = special-soundness }

    Σ-sig : Σ-Signature
    Σ-sig = _

    Σ-structure : Σ-Structure Valid
    Σ-structure = record { Σ-sig = Σ-sig ; special-Σ-protocol = special-Σ-protocol }

  -- This now subsumed by Generic (g₀ ∷ g₁ ∷ []) (u₀ ∷ u₁ ∷ [])
  module Generic2 (g₀ g₁ u₀ u₁ : G) where
    Commitment : ★
    Commitment = G × G

    _∈Y : Witness → Type
    w ∈Y = (g₀ ^ w ≡ u₀) × (g₁ ^ w ≡ u₁)

    open ΣProto Commitment Challenge Response Randomness Witness _∈Y public

    prover : Prover
    prover x w = commitment ΣTypes., response
     module CPProver where
      commitment : Commitment
      commitment = (g₀ ^ x) , (g₁ ^ x)

      response : Challenge → Response
      response c = x + (w * c)

    verifier : Verifier
    verifier (mk (A , B) c s) = check₀ ∧ check₁ 
      module CPVerifier where
        check₀ = (g₀ ^ s) == (A · (u₀ ^ c))
        check₁ = (g₁ ^ s) == (B · (u₁ ^ c))

    ChaumPedersen : Σ-Protocol
    ChaumPedersen = prover , verifier

    -- This simulator shows why it is so important for the
    -- challenge to be picked once the commitment is known.
    --
    -- To fake a transcript, the challenge and response can
    -- be arbitrarily chosen. However to be indistinguishable
    -- from a valid proof it they need to be picked at random.
    simulator : Simulator
    simulator c s = simulated-commitment
      module CPSimulator where

        -- Compute A and B, such that the verifier accepts!
        A = (g₀ ^ s) / (u₀ ^ c)
        B = (g₁ ^ s) / (u₁ ^ c)

        simulated-commitment : Commitment
        simulated-commitment = (A , B)

        simulated-transcript : Transcript
        simulated-transcript = ΣTypes.mk simulated-commitment c s

    -- The extractor shows the importance of never reusing a
    -- commitment. If the prover answers to two different challenges
    -- comming from the same commitment then the knowledge of the
    -- prover (the witness) can be extracted.
    extractor : Extractor verifier
    extractor t² = w'
        module Witness-extractor where
          open Transcript² t²
          fd = get-f₀ − get-f₁
          cd = get-c₀ − get-c₁
          w' = fd * cd ⁻¹

    open ≡-Reasoning

    shvzk : Special-Honest-Verifier-Zero-Knowledge ChaumPedersen
    shvzk = record { correct-simulator = λ _ _ → ✓∧ (≡⇒== /-·) (≡⇒== /-·) }

    correct : Correct (prover , verifier)
    correct w x c (e₀ , e₁) = ✓∧ (≡⇒== pf₀) (≡⇒== pf₁)
      where

        A = g₀ ^ x
        pf₀ = g₀ ^(x + (w * c))
            ≡⟨ ^-+ ⟩
              A · (g₀ ^(w * c))
            ≡⟨ ap (λ z → A · z) ^-* ⟩
              A · ((g₀ ^ w) ^ c)
            ≡⟨ ap (λ z → A · (z ^ c)) e₀ ⟩
              A · (u₀ ^ c)
            ∎

        -- TODO repeating the proof above
        B = g₁ ^ x
        pf₁ = g₁ ^(x + (w * c))
            ≡⟨ ^-+ ⟩
              B · (g₁ ^(w * c))
            ≡⟨ ap (λ z → B · z) ^-* ⟩
              B · ((g₁ ^ w) ^ c)
            ≡⟨ ap (λ z → B · (z ^ c)) e₁ ⟩
              B · (u₁ ^ c)
            ∎

    module _ (t² : Transcript² verifier) where
      open Transcript² t² renaming (get-A to AB; get-c₀ to c₀; get-c₁ to c₁
                                   ;get-f₀ to f₀; get-f₁ to f₁)
      A = fst AB
      B = snd AB
      module V₀ = CPVerifier A B c₀ f₀
      module V₁ = CPVerifier A B c₁ f₁
      module Lemma' = ZK.Lemmas cg c₀ c₁ f₀ f₁
      open Witness-extractor t²

      .u₀-ok : g₀ ^ w' ≡ u₀
      u₀-ok = Lemma'.proof A u₀ g₀ (✓∧₁ verify₀) (✓∧₁ verify₁)

      .u₁-ok : g₁ ^ w' ≡ u₁
      u₁-ok = Lemma'.proof B u₁ g₁ (✓∧₂ {V₀.check₀} verify₀) (✓∧₂ {V₁.check₀} verify₁)

      -- The extracted w' is correct
      .extractor-ok : w' ∈Y
      extractor-ok = u₀-ok , u₁-ok

    -- All of this should not be in proofs...
    special-soundness : Special-Soundness ChaumPedersen
    special-soundness = record { extract-valid-witness = extractor-ok }

    special-Σ-protocol : Special-Σ-Protocol
    special-Σ-protocol = record { correct = correct ; shvzk = shvzk ; ssound = special-soundness }

    Σ-sig : Σ-Signature
    Σ-sig = _

    Σ-structure : Σ-Structure _∈Y
    Σ-structure = record { Σ-sig = Σ-sig ; special-Σ-protocol = special-Σ-protocol }

  -- TODO: Re-use another module
  module ElGamal-encryption where
    record CipherText : ★ where
      constructor _,_
      field
        α β : G

    PubKey  = G
    PrivKey = ℤq
    EncRnd  = ℤq {- randomness used for encryption of ct -}
    Message = G {- plain text message -}

    enc : PubKey → EncRnd → Message → CipherText
    enc y r M = α , β where
      α = g ^ r
      β = (y ^ r) · M

    dec : PrivKey → CipherText → Message
    dec x ct = β / (α ^ x) where
      open CipherText ct

  open ElGamal-encryption

  -- CP : (g₀ g₁ u₀ u₁ : G) (w : ℤq) → Type
  -- CP g₀ g₁ u₀ u₁ w = (g₀ ^ w ≡ u₀) × (g₁ ^ w ≡ u₁)

  CP : (g₀ g₁ u₀ u₁ : G) (w : ℤq) → Type
  CP g₀ g₁ u₀ u₁ w = ✓ ((g₀ ^ w == u₀) ∧ (g₁ ^ w == u₁))

  module _ (y  : PubKey)
           (M  : Message)
           (ct : CipherText)
           where
    module CT = CipherText ct

    KnownEncRnd : EncRnd → Type
    KnownEncRnd r = enc y r M ≡ ct

    module GenKnownEncRnd = Generic (g ∷ y ∷ []) (CT.α ∷ (CT.β / M) ∷ [])

    mapEncRnd : W-Map GenKnownEncRnd.Valid KnownEncRnd
    mapEncRnd = record { →Witness = id ; ←Witness = id
                       ; →Valid = λ w₀? → let (p₀ , p₁₂) = ✓∧× w₀?
                                              (p₁ , p₂)  = ✓∧× p₁₂ in
                                          ap₂ _,_ (==⇒≡ p₀) (pf (==⇒≡ p₁))
                       ; ←Valid = λ w₁? → ✓∧ (≡⇒== (ap CipherText.α w₁?))
                                             (✓∧ (≡⇒== (pf! (ap CipherText.β w₁?))) _)
                       }
     where
      pf : ∀ {M yr β} → yr ≡ β / M → yr · M ≡ β
      pf {M} e = ap (flip _·_ M) e ∙ ! /-·

      pf! : ∀ {M yr β} → yr · M ≡ β → yr ≡ β / M
      pf! {M} e = ·-/ ∙ ap (flip _/_ M) e

    module σEncRndKnowledge = Apply-W-Map mapEncRnd GenKnownEncRnd.Σ-structure

    KnownDec : PrivKey → Type
    KnownDec x = (g ^ x ≡ y) × (dec x ct ≡ M)

    module GenKnownDec = Generic (g ∷ CT.α ∷ []) (y ∷ (CT.β / M) ∷ [])

    mapDec : W-Map GenKnownDec.Valid KnownDec
    mapDec = record { →Witness = id ; ←Witness = id
                    ; →Valid = λ w₀? → let (p₀ , p₁₂) = ✓∧× w₀?
                                           (p₁ , p₂)  = ✓∧× p₁₂ in
                                       ==⇒≡ p₀ , pf (==⇒≡ p₁)
                    ; ←Valid = λ w₁? → ✓∧ (≡⇒== (fst w₁?))
                                          (✓∧ (≡⇒== (pf! (snd w₁?))) _)
                    }
     where
      pf : ∀ {w M} → CT.α ^ w ≡ CT.β / M → dec w ct ≡ M
      pf {w} {M} e = ap (_/_ CT.β) e ∙ ! /-/

      pf! : ∀ {w M} → dec w ct ≡ M → CT.α ^ w ≡ CT.β / M
      pf! {w} {M} e = /-/ ∙ ap (_/_ CT.β) e

    module σKnownDec = Apply-W-Map mapEncRnd GenKnownEncRnd.Σ-structure
-- -}
-- -}
-- -}
-- -}
