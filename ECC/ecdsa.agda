
open import Data.Bool
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality.NP

module _ where

𝟚 = Bool
pattern 0₂ = false
pattern 1₂ = true

postulate
  Point ℤq : Set
  get-x get-y : Point → ℤq
  G : Point
  _·_  : ℤq → Point → Point
  _+ₚ_ : Point → Point → Point
  _+_ _*_ : ℤq → ℤq → ℤq
  modinv : ℤq → ℤq
  _==_  : ℤq → ℤq → Bool
  from-x : ℤq → 𝟚 → Point
  -1 : ℤq

_-ₚ_ : Point → Point → Point
P -ₚ Q = P +ₚ -1 · Q

infixr 8 _·_
infixl 6 _+_ _+ₚ_ _-ₚ_
infixl 7 _*_
{-
_+_ = plus
_*_ = mult
-}


record Signature : Set where
  constructor _,_
  field
    get-Rx : ℤq
    get-s  : ℤq


module Scalar where

    Sign : (h r sk : ℤq) → Signature
    Sign h r sk = sig
      module Sign where
        R   = r · G
        Rx  = get-x R -- % N
        s   = (h + Rx * sk) * modinv r
        sig = (Rx , s)

-- TODO Malleability
-- Mutate (Rx , s) = (Rx , 0 - s)
-- Mutate != id
-- Malleable = ∀ h r sk → Verify h (Mutate (Sign h r sk)) (sk · G) ≡ true

    Verify : (h : ℤq) (sig : Signature) (Pk : Point) → Bool
    Verify h (Rx , s) Pk = Rx == get-x u
      module Verify where
        w  = modinv s
        u1 = (h  * w) · G
        u2 = (Rx * w) · Pk
        u  = u1 +ₚ u2

    {-
    Recovery : (h : ℤq) → Signature → (Point × Point)
    Recovery h sig = Recovery_ 0₂ h sig , Recovery_ 1₂ h sig
    -}

    Correctness = ∀ h r sk → Verify h (Sign h r sk) (sk · G) ≡ true

    Recovery_ : (b : 𝟚) (h : ℤq) → Signature → Point
    Recovery_ b h (Rx , s) = Pk
      where
        R    = from-x Rx b
        Rx⁻¹ = modinv Rx
        hG   = h · G
        Pk   = Rx⁻¹ · (s · R -ₚ hG)
{-
sR = (s*r) · G
sR - hG = ((s * r)-h) · G
        = Rx · sk · G
        = Rx · Pk
s = (h + Rx * sk) * modinv r
s*r = h + Rx * sk
s*r - h = Rx * sk

-}

    CorrectRecovery =
      ∀ h r sk →
        Recovery_ 0₂ h (Sign h r sk) ≡ (sk · G)
        ⊎
        Recovery_ 1₂ h (Sign h r sk) ≡ (sk · G)

    module Correctness
       (==-reflexivity : ∀ {x y} → x ≡ y → x == y ≡ true)

       (+-*-distr : ∀ {x y z} → (x + y) * z ≡ x * z  + y * z)
       (modinv-*-distr : ∀ {x y} → modinv (x * y) ≡ modinv x * modinv y)
       (modinv-modinv : ∀ {x} → modinv (modinv x) ≡ x)
       (*-assoc : ∀ {x y z} → (x * y) * z ≡ x * (y * z))
       (*-comm : ∀ {x y} → x * y ≡ y * x)
       (modinv-cancel : ∀ {x y} → x * modinv x * y ≡ y)

       (+-·-distr : ∀ {x y P} → (x + y) · P ≡ x · P +ₚ y · P)
       (*-·-distr : ∀ {x y P} → (x * y) · P ≡ x · y · P)
       where

        correct : Correctness
        correct h r sk = ==-reflexivity (ap get-x (! ue))
          where
            open ≡-Reasoning
            pk = sk · G
            open Sign h r sk
            open Verify h Rx s pk
            u2e = u2
                ≡⟨ ! *-·-distr ⟩
                  ((Rx * w) * sk) · G
                ≡⟨ ap (λ x → x · G) *-assoc ⟩
                  (Rx * (w * sk)) · G
                ≡⟨ ap (λ x → x · G) (ap (λ y → Rx * y) *-comm) ⟩
                  (Rx * (sk * w)) · G
                ≡⟨ ap (λ x → x · G) (! *-assoc) ⟩
                  (Rx * sk * w) · G
                ∎
            z = h + Rx * sk
            ue = u
               ≡⟨by-definition⟩
                 u1 +ₚ u2
               ≡⟨ ap (_+ₚ_ u1) u2e ⟩
                 u1 +ₚ (Rx * sk * w) · G
               ≡⟨ ! +-·-distr ⟩
                 (h * w + Rx * sk * w) · G
               ≡⟨ ap (λ x → x · G) (! +-*-distr) ⟩
                 (z * w) · G
               ≡⟨by-definition⟩
                 (z * modinv (z * modinv r)) · G
               ≡⟨ ap (λ x → (z * x) · G) modinv-*-distr ⟩
                 (z * (modinv z * modinv (modinv r))) · G
               ≡⟨ ap (λ x → (z * (modinv z * x)) · G) modinv-modinv ⟩
                 (z * (modinv z * r)) · G
               ≡⟨ ap (λ x → x · G) (! *-assoc) ⟩
                 ((z * modinv z) * r) · G
               ≡⟨ ap (λ x → x · G) modinv-cancel ⟩
                 r · G
               ∎

        module _
          (from-get-x :
            ∀ P →
              from-x (get-x P) 0₂ ≡ P ⊎ from-x (get-x P) 1₂ ≡ P)
          (get-from-x : ∀ x b → get-x (from-x x b) ≡ x)
          (·-+ₚ-distr : ∀ {x P Q} → x · (P +ₚ Q) ≡ x · P +ₚ x · Q)
          (·-subₚ-distr : ∀ {x P Q} → x · (P -ₚ Q) ≡ x · P -ₚ x · Q)
          where
            open ≡-Reasoning
            module _ {h r sk Rx : ℤq} where
                Rx⁻¹ = modinv Rx
                r⁻¹  = modinv r

                helper1' = ((h + Rx * sk) * r⁻¹) · r · G
                         ≡⟨ {!!} ⟩
                           (h + Rx * sk) · G
                         ∎

                helper
                  = Rx⁻¹ · (((h + Rx * sk) * r⁻¹) · r · G -ₚ h · G)
                  ≡⟨ ·-subₚ-distr ⟩
                    (Rx⁻¹ · ((h + Rx * sk) * r⁻¹) · r · G) -ₚ (Rx⁻¹ · h · G)
                  ≡⟨ {!!} ⟩
                    (Rx⁻¹ · ((h + Rx * sk) * r⁻¹ * r) · G) -ₚ (Rx⁻¹ · h · G)
                  ≡⟨ {!!} ⟩
                    (Rx⁻¹ · (h + Rx * sk) · G) -ₚ (Rx⁻¹ · h · G)
                  ≡⟨ {!!} ⟩
                    ((Rx⁻¹ * Rx * sk) · G)
                  ≡⟨ {!!} ⟩
                    sk · G
                  ∎

            correct-recovery : CorrectRecovery
            correct-recovery h r sk with from-get-x (r · G)
            ... | inl e rewrite e = inl helper
            ... | inr e rewrite e = inr helper

module Hashed
  (Message : Set)
  (H : Message → ℤq)
  where
    Sign : (m : Message) (r sk : ℤq) → Signature
    Sign m = Scalar.Sign (H m)

    Verify : (m : Message) (sig : Signature) (pk : Point) → Bool
    Verify m = Scalar.Verify (H m)
-- -}
-- -}
-- -}
-- -}
